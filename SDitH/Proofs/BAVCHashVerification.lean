import SDitH.Spec.BAVCHashVerification
import SDitH.Proofs.BAVCBindingROM
import SDitH.Proofs.OracleProgram
import SDitH.Proofs.RandomOraclePipeline

namespace SDitH.Proofs.BAVCHashVerification

open Spec.BAVC Spec.BAVCBinding Spec.BAVCBindingROM Spec.BAVCHashVerification
open Spec.OracleProgram Spec.RandomOracleCollision
open scoped Classical ENNReal
noncomputable section

variable {lambda tau N : Nat} {State : Type*}

theorem root_bounded (salt : Seed lambda) (commits : Commitments lambda tau N) :
    Bounded (tau + 1) (rootProgram salt commits) := by
  exact OracleProgram.bounded_bind _ _ tau 1 (OracleProgram.bounded_array _ _) (fun _ _ => trivial)

theorem verify_bounded (claim : Claim lambda tau N) :
    Bounded (verificationBudget tau) (verifyProgram claim) := by
  rw [verificationBudget, two_mul]
  apply OracleProgram.bounded_bind _ _ (tau + 1) (tau + 1) (root_bounded _ _)
  intro leftRoot
  simpa only [Nat.add_zero] using OracleProgram.bounded_bind
    (rootProgram claim.rightSalt claim.right) (fun rightRoot => .done (Checked.mk claim leftRoot rightRoot))
    (tau + 1) 0 (root_bounded _ _) (fun _ => trivial)

/-- The row/outer lookup coverage and exact source root follow from execution
of the program. The table fallback plays no role in any of these queries. -/
theorem root_evaluates (p : Primitives lambda) (table : List Bool → Option (Digest lambda))
    (salt : Seed lambda) (commits : Commitments lambda tau N) (root : Digest lambda)
    (h : Evaluates table (rootProgram salt commits) root) :
    observed p table salt commits = true ∧ rootHash (withTable p table) salt commits = root := by
  obtain ⟨rows, hrows, htail⟩ := (OracleProgram.evaluates_bind _ _ _ _).mp h
  have hr := OracleProgram.evaluates_array table tau (rowQuery commits) rows hrows
  have heq : rows = fun e => (withTable p table).hash (rowQuery commits e) := by
    funext e
    simp [withTable, hr e]
  cases htail with
  | query _ _ answer _ stored hdone =>
    cases hdone
    rw [heq] at stored
    have ho : table (outerQuery (withTable p table) salt commits) = some root := stored
    refine ⟨?_, ?_⟩
    · apply List.all_eq_true.mpr
      intro input hin
      simp only [hashQueries, List.mem_append, List.mem_ofFn, List.mem_singleton] at hin
      rcases hin with ⟨e, rfl⟩ | rfl
      · simp [hr e]
      · simp [ho]
    · change (table (outerQuery (withTable p table) salt commits)).getD (fun _ => false) = root
      rw [ho]
      rfl

theorem verify_evaluates (p : Primitives lambda) (table : List Bool → Option (Digest lambda))
    (claim : Claim lambda tau N) (checked : Checked lambda tau N)
    (h : Evaluates table (verifyProgram claim) checked) :
    checked.claim = claim ∧ observed p table checked.claim.leftSalt checked.claim.left = true ∧
      observed p table checked.claim.rightSalt checked.claim.right = true ∧
      rootHash (withTable p table) checked.claim.leftSalt checked.claim.left = checked.leftRoot ∧
      rootHash (withTable p table) checked.claim.rightSalt checked.claim.right = checked.rightRoot := by
  obtain ⟨leftRoot, hl, htail⟩ := (OracleProgram.evaluates_bind _ _ _ _).mp h
  obtain ⟨rightRoot, hr, hdone⟩ := (OracleProgram.evaluates_bind _ _ _ _).mp htail
  cases hdone
  have hleft := root_evaluates p table claim.leftSalt claim.left leftRoot hl
  have hright := root_evaluates p table claim.rightSalt claim.right rightRoot hr
  exact ⟨rfl, hleft.1, hright.1, hleft.2, hright.2⟩

/-- Every supported run finishes both computations. Their coverage and source
root equations are proved, including queries not made by the adversary. -/
theorem experiment_complete (p : Primitives lambda)
    (adversary : Procedure (List Bool) (Digest lambda) State) (q : Nat) (initial : State)
    (choose : State → Claim lambda tau N)
    (out : Result (List Bool) (Digest lambda) (VerificationState lambda tau N))
    (hout : out ∈ (Spec.BAVCHashVerification.experiment adversary q initial choose).support) :
    ∃ checked, out.state = .done checked ∧
      observed p out.table checked.claim.leftSalt checked.claim.left = true ∧
      observed p out.table checked.claim.rightSalt checked.claim.right = true ∧
      rootHash (withTable p out.table) checked.claim.leftSalt checked.claim.left = checked.leftRoot ∧
      rootHash (withTable p out.table) checked.claim.rightSalt checked.claim.right = checked.rightRoot := by
  obtain ⟨start, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst out
  obtain ⟨checked, hc, heval⟩ := OracleProgram.run_evaluates (verifyProgram (choose start.state))
    (verificationBudget tau) (verify_bounded _) start.table start.history tail ht
  exact ⟨checked, hc, (verify_evaluates p tail.table (choose start.state) checked heval).2⟩

theorem winning_collision (p : Primitives lambda)
    (adversary : Procedure (List Bool) (Digest lambda) State) (q : Nat) (initial : State)
    (choose : State → Claim lambda tau N)
    (out : Result (List Bool) (Digest lambda) (VerificationState lambda tau N))
    (hout : out ∈ (Spec.BAVCHashVerification.experiment adversary q initial choose).support)
    (hwin : wins out = true) : ∃ pair, storedCollision pair out = true := by
  obtain ⟨checked, hc, hleft, hright, hlroot, hrroot⟩ := experiment_complete p adversary q initial choose out hout
  have hw : checked.leftRoot = checked.rightRoot ∧
      (checked.claim.leftSalt ≠ checked.claim.rightSalt ∨ checked.claim.left ≠ checked.claim.right) := by
    simpa only [wins, hc, decide_eq_true_eq] using hwin
  have hclaim : claimWins p checked.claim out = true := by
    simp only [claimWins, hleft, hright, Bool.true_and, decide_eq_true_eq]
    exact ⟨hlroot.trans (hw.1.trans hrroot.symm), hw.2⟩
  obtain ⟨pair, _, hs⟩ := BAVCBindingROM.winning_claim_collision p checked.claim out hclaim
  exact ⟨pair, hs⟩

/-- Hash binding with verification queries included, rather than assumed
present: the total budget is q + 2*(tau+1). This is not seed/BLC binding or
signature security; it establishes the hash part for adaptively chosen data. -/
theorem binding_probability_bound (p : Primitives lambda)
    (adversary : Procedure (List Bool) (Digest lambda) State) (q : Nat) (initial : State)
    (choose : State → Claim lambda tau N) :
    ((Spec.BAVCHashVerification.experiment adversary q initial choose).map wins) true ≤
      ((q + 2 * (tau + 1)).choose 2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (2 * lambda) := by
  have h := RandomOraclePipeline.event_bound adversary q initial Spec.OracleProgram.procedure
    (verificationBudget tau) (fun state => verifyProgram (choose state)) wins
    (fun out hout hwin => winning_collision p adversary q initial choose out hout hwin)
  convert h using 1
  simp [verificationBudget, Digest, Spec.DomainSeparation.Bits, ENNReal.inv_pow]

end
end SDitH.Proofs.BAVCHashVerification
