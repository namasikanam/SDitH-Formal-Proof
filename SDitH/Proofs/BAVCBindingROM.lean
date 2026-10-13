import SDitH.Spec.BAVCBindingROM
import SDitH.Proofs.BAVCBinding
import SDitH.Proofs.RandomOracleCollisionInvariant

namespace SDitH.Proofs.BAVCBindingROM

open Spec.BAVC Spec.BAVCBinding Spec.BAVCBindingROM Spec.RandomOracleCollision
open scoped Classical ENNReal
noncomputable section

variable {lambda tau N : Nat} {State : Type*}

theorem observed_lookup (p : Primitives lambda) (table : List Bool → Option (Digest lambda))
    (salt : Seed lambda) (commits : Commitments lambda tau N)
    (h : observed p table salt commits = true) (input : List Bool)
    (hinput : input ∈ hashQueries (withTable p table) salt commits) :
    table input = some ((withTable p table).hash input) := by
  have hs := List.all_eq_true.mp h input hinput
  cases he : table input with
  | none => simp [he] at hs
  | some answer => simp [withTable, he]

/-- A successful fully queried binding claim makes the actual finder return
two distinct stored inputs with the same answer. No binding property is assumed. -/
theorem winning_claim_collision (p : Primitives lambda) (claim : Claim lambda tau N)
    (out : Result (List Bool) (Digest lambda) State) (hwin : claimWins p claim out = true) :
    ∃ pair, findHashCollision (withTable p out.table) claim.leftSalt claim.rightSalt claim.left claim.right = some pair ∧
      storedCollision pair out = true := by
  have hw := hwin
  simp only [claimWins, Bool.and_eq_true, decide_eq_true_eq] at hw
  cases he : findHashCollision (withTable p out.table) claim.leftSalt claim.rightSalt claim.left claim.right with
  | none =>
    have heq := BAVCBinding.find_none_implies_equal _ _ _ _ _ he
    exact False.elim (hw.2.2.elim (fun h => h heq.1) (fun h => h heq.2))
  | some pair =>
    have hc := BAVCBinding.find_some_collision _ _ _ _ _ hw.2.1 pair he
    refine ⟨pair, rfl, ?_⟩
    simp only [storedCollision, decide_eq_true_eq]
    refine ⟨hc.1.1, (withTable p out.table).hash pair.1, ?_, ?_⟩
    · exact observed_lookup p out.table claim.leftSalt claim.left hw.1.1 pair.1 hc.2.1
    · rw [hc.1.2]
      exact observed_lookup p out.table claim.rightSalt claim.right hw.1.2 pair.2 hc.2.2

theorem winning_selection (p : Primitives lambda)
    (choose : Result (List Bool) (Digest lambda) State → Option (Claim lambda tau N))
    (out : Result (List Bool) (Digest lambda) State) (hwin : bindingWins p choose out = true) :
    selectionWins (collisionSelector p choose) out = true := by
  cases he : choose out with
  | none => simp [bindingWins, he] at hwin
  | some claim =>
    have hc : claimWins p claim out = true := by simpa only [bindingWins, he] using hwin
    obtain ⟨pair, hp, hs⟩ := winning_claim_collision p claim out hc
    simpa only [selectionWins, collisionSelector, he, Option.bind_some, hc, Bool.true_eq,
      if_true, hp] using hs

/-- Quantitative binding for the actual two-layer Hashbavc strings once both
computations have been queried. All adaptive oracle calls count toward budget.
This bound does not cover seed collisions or assert a full BLC/signature bound. -/
theorem binding_probability_bound (p : Primitives lambda)
    (procedure : Procedure (List Bool) (Digest lambda) State) (budget : Nat) (initial : State)
    (choose : Result (List Bool) (Digest lambda) State → Option (Claim lambda tau N)) :
    ((experiment procedure budget initial).map (bindingWins p choose)) true ≤
      (budget.choose 2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (2 * lambda) := by
  have h := RandomOracleCollisionInvariant.selection_collision_bound procedure budget initial
    (collisionSelector p choose)
  have hm : ((experiment procedure budget initial).map (bindingWins p choose)) true ≤
      ((experiment procedure budget initial).map (selectionWins (collisionSelector p choose))) true := by
    simp only [PMF.map_apply]
    apply ENNReal.tsum_le_tsum
    intro out
    by_cases hw : bindingWins p choose out = true
    · simp [hw, winning_selection p choose out hw]
    · simp [hw]
  apply hm.trans
  convert h using 1
  simp [Digest, Spec.DomainSeparation.Bits, ENNReal.inv_pow]

end
end SDitH.Proofs.BAVCBindingROM
