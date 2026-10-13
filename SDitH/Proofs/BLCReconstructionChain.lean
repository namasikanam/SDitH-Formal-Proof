import SDitH.Spec.BLCReconstructionChain
import SDitH.Proofs.BLCHashChain
import SDitH.Proofs.BAVCReconstructionGame
import SDitH.Proofs.SeedPairBinding

/-! Both selected reconstructions, each followed by the verifier's actual
Hashaux/Hashlines chain, execute after a mixed adversary on the shared
hash/cipher oracle. Equal final line digests with a disagreeing commonly
revealed seed yield a stored hash collision or a covered seed collision.
The intervening computations are explicit bounded oracle programs supplied by
the caller; nothing here implements Algorithm 12's missing bindings or its
ill-typed line 21, and no signature acceptance or extraction is claimed. -/

namespace SDitH.Proofs.BLCReconstructionChain

open Spec.DomainSeparation Spec.BAVC Spec.BAVCCipherProgram Spec.BAVCReconstructionProgram
open Spec.BLCHashChain Spec.BLCReconstructionChain Spec.HashCipherProgram Spec.HashCipherEvaluation
open scoped Classical ENNReal
noncomputable section

variable {lambda tau N : Nat} {Key Block Context Error State : Type*}

theorem bounded_done {A : Type*} (n : Nat) (value : A) :
    Bounded n (Program.done value : Program (List Bool) (Digest lambda) Key Block A) := by
  cases n <;> trivial

theorem open_bounded (layout : Layout lambda Key Block) (variant : Grinding) (Topen p m : Nat)
    (input : Input lambda tau N Key Block Context Error) (hb : Bounds p m input) :
    Bounded (openingBudget tau N p m) (openProgram layout variant Topen input) := by
  rw [openingBudget, Nat.add_assoc]
  unfold openProgram
  apply HashCipherProgram.bounded_bind _ _ (budget tau N) (p + (m + 2))
    (BAVCReconstructionProgram.reconstruction_bounded layout variant input.opening.salt input.opening.hidden
      input.opening.opening Topen input.opening.nodes)
  intro result
  cases result with
  | error cause => exact bounded_done _ _
  | ok reconstruction =>
    apply HashCipherProgram.bounded_bind _ _ p (m + 2) (hb.1 reconstruction)
    intro before
    cases before with
    | error cause => exact bounded_done _ _
    | ok context =>
      exact HashCipherProgram.bounded_mono _ _ _ (Nat.le_of_eq (Nat.add_zero _))
        (HashCipherProgram.bounded_bind _ _ (m + 2) 0
          (BLCHashChain.partial_bounded reconstruction.hcom input.auxiliaryTail
            (input.afterAux reconstruction context) m (hb.2 reconstruction context))
          (fun _ => bounded_done _ _))

theorem verify_bounded (layout : Layout lambda Key Block) (variant : Grinding) (Topen p m : Nat)
    (claim : Claim lambda tau N Key Block Context Error) (hl : Bounds p m claim.left) (hr : Bounds p m claim.right) :
    Bounded (verificationBudget tau N p m) (verifyProgram layout variant Topen claim) := by
  rw [verificationBudget, two_mul]
  apply HashCipherProgram.bounded_bind _ _ (openingBudget tau N p m) (openingBudget tau N p m)
    (open_bounded layout variant Topen p m claim.left hl)
  intro left
  exact HashCipherProgram.bounded_bind _ _ (openingBudget tau N p m) 0
    (open_bounded layout variant Topen p m claim.right hr) (fun _ => bounded_done _ _)

/-- A successful chain output carries a successful reconstruction evaluation,
some successful intermediate context, and the two actual hash lookups. -/
theorem open_evaluates (layout : Layout lambda Key Block) (variant : Grinding) (Topen : Nat)
    (input : Input lambda tau N Key Block Context Error) (family : Spec.IdealCipher.Family Key Block)
    (table : List Bool → Option (Digest lambda)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (value : Value lambda tau N)
    (h : Evaluates family table ciphers (openProgram layout variant Topen input) (Except.ok value)) :
    Evaluates family table ciphers
      (Spec.BAVCReconstructionProgram.reconstruct layout variant input.opening.salt input.opening.hidden
        input.opening.opening Topen input.opening.nodes) (Except.ok value.reconstruction) ∧
    ∃ context, Evaluates family table ciphers (input.beforeAux value.reconstruction) (Except.ok context) ∧
      Evaluates family table ciphers
        (partialProgram value.reconstruction.hcom input.auxiliaryTail (input.afterAux value.reconstruction context))
        (Except.ok value.hashes) := by
  obtain ⟨result, hr, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
  cases result with
  | error cause => cases ht
  | ok reconstruction =>
    obtain ⟨before, hb, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp ht
    cases before with
    | error cause => cases ht
    | ok context =>
      obtain ⟨after, ha, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp ht
      cases after with
      | error cause => cases ht
      | ok hashes =>
        cases ht
        exact ⟨hr, context, hb, ha⟩

theorem verify_evaluates (layout : Layout lambda Key Block) (variant : Grinding) (Topen : Nat)
    (claim : Claim lambda tau N Key Block Context Error) (family : Spec.IdealCipher.Family Key Block)
    (table : List Bool → Option (Digest lambda)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (checked : Checked lambda tau N Key Block Context Error)
    (h : Evaluates family table ciphers (verifyProgram layout variant Topen claim) checked) :
    checked.claim = claim ∧
      Evaluates family table ciphers (openProgram layout variant Topen claim.left) checked.left ∧
      Evaluates family table ciphers (openProgram layout variant Topen claim.right) checked.right := by
  obtain ⟨left, hl, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ checked).mp h
  obtain ⟨right, hr, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ checked).mp ht
  cases ht
  exact ⟨rfl, hl, hr⟩

/-- Equal line digests give equal roots or a stored collision on the exact
Aux/Lines queries; equal roots with a disagreeing revealed seed then reduce
through the existing reconstruction collision finder. -/
theorem evaluated_collision (layout : Layout lambda Key Block) (variant : Grinding) (Topen : Nat)
    (claim : Claim lambda tau N Key Block Context Error) (family : Spec.IdealCipher.Family Key Block)
    (out : Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block State)
    (left right : Value lambda tau N)
    (hl : Evaluates family out.hashTable out.cipherHistory (openProgram layout variant Topen claim.left) (Except.ok left))
    (hr : Evaluates family out.hashTable out.cipherHistory (openProgram layout variant Topen claim.right) (Except.ok right))
    (hlines : left.hashes.lines = right.hashes.lines) (e : Fin tau) (i : Fin N) (leftSeed rightSeed : Seed lambda)
    (hls : left.reconstruction.seeds e i = some leftSeed) (hrs : right.reconstruction.seeds e i = some rightSeed)
    (hne : leftSeed ≠ rightSeed) :
    (∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView out) = true) ∨
      (claim.left.opening.salt = claim.right.opening.salt ∧
        Spec.BAVCBinding.IsSeedCollision (primitives (tau := tau) (N := N) layout variant family out.hashTable)
          claim.left.opening.salt (Spec.SeedTree.leafOffset e i) leftSeed rightSeed ∧
        ∀ side : Bool,
          Spec.IdealCipher.entry (.encrypt (layout.key leftSeed)
            (layout.input (Spec.SeedPrimitives.cipherInput variant claim.left.opening.salt (tau * N + Spec.SeedTree.leafOffset e i) side)))
            (family (layout.key leftSeed) (layout.input (Spec.SeedPrimitives.cipherInput variant claim.left.opening.salt (tau * N + Spec.SeedTree.leafOffset e i) side))) ∈ out.cipherHistory ∧
          Spec.IdealCipher.entry (.encrypt (layout.key rightSeed)
            (layout.input (Spec.SeedPrimitives.cipherInput variant claim.left.opening.salt (tau * N + Spec.SeedTree.leafOffset e i) side)))
            (family (layout.key rightSeed) (layout.input (Spec.SeedPrimitives.cipherInput variant claim.left.opening.salt (tau * N + Spec.SeedTree.leafOffset e i) side))) ∈ out.cipherHistory) := by
  obtain ⟨hlr, lc, _, hla⟩ := open_evaluates layout variant Topen claim.left family out.hashTable out.cipherHistory left hl
  obtain ⟨hrr, rc, _, hra⟩ := open_evaluates layout variant Topen claim.right family out.hashTable out.cipherHistory right hr
  rcases BLCHashChain.partial_equal_lines_root_or_collision family out left.reconstruction.hcom right.reconstruction.hcom
    claim.left.auxiliaryTail claim.right.auxiliaryTail _ _ left.hashes right.hashes hla hra hlines with hroot | hc
  · exact BAVCReconstructionGame.evaluated_collision layout variant Topen ⟨claim.left.opening, claim.right.opening⟩
      family out left.reconstruction right.reconstruction hlr hrr hroot e i leftSeed rightSeed hls hrs hne
  · exact Or.inl hc

variable [Fintype Key] [Fintype Block]

theorem joint_complete (layout : Layout lambda Key Block) (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N Key Block Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right)
    (joint : Spec.IdealCipher.Family Key Block × Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block
      (ChainProgram lambda Key Block (Checked lambda tau N Key Block Context Error)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N p m)
      (fun state => verifyProgram layout variant Topen (choose state))).support) :
    ∃ checked, joint.2.state = .done checked ∧
      Evaluates joint.1 joint.2.hashTable joint.2.cipherHistory (verifyProgram layout variant Topen checked.claim) checked := by
  obtain ⟨start, _, tail, ht, he⟩ := HashCipherPipeline.joint_decompose adversary q initial procedure (verificationBudget tau N p m)
    (fun state => verifyProgram layout variant Topen (choose state)) joint hout
  obtain ⟨checked, hs, hv⟩ := HashCipherEvaluation.run_evaluates joint.1 _ (verificationBudget tau N p m)
    (verify_bounded layout variant Topen p m (choose start.state) (hbounds start.state).1 (hbounds start.state).2)
    start.hashTable start.hashHistory start.cipherHistory tail ht
  have hc := (verify_evaluates layout variant Topen (choose start.state) joint.1 tail.hashTable tail.cipherHistory checked hv).1
  rw [← hc] at hv
  exact ⟨checked, by simpa only [he, Spec.HashCipher.markHash] using hs, by simpa only [he, Spec.HashCipher.markHash] using hv⟩

theorem winning_evaluations (layout : Layout lambda Key Block) (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N Key Block Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right)
    (joint : Spec.IdealCipher.Family Key Block × Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block
      (ChainProgram lambda Key Block (Checked lambda tau N Key Block Context Error)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N p m)
      (fun state => verifyProgram layout variant Topen (choose state))).support)
    (hwin : wins joint.2 = true) :
    ∃ (claim : Claim lambda tau N Key Block Context Error) (left right : Value lambda tau N) (e : Fin tau) (i : Fin N)
      (leftSeed rightSeed : Seed lambda),
      Evaluates joint.1 joint.2.hashTable joint.2.cipherHistory (openProgram layout variant Topen claim.left) (Except.ok left) ∧
      Evaluates joint.1 joint.2.hashTable joint.2.cipherHistory (openProgram layout variant Topen claim.right) (Except.ok right) ∧
      left.hashes.lines = right.hashes.lines ∧ left.reconstruction.seeds e i = some leftSeed ∧
      right.reconstruction.seeds e i = some rightSeed ∧ leftSeed ≠ rightSeed := by
  obtain ⟨checked, hs, hv⟩ := joint_complete layout variant Topen p m adversary q initial choose hbounds joint hout
  have he := verify_evaluates layout variant Topen checked.claim joint.1 joint.2.hashTable joint.2.cipherHistory checked hv
  cases hl : checked.left with
  | error cause => simp only [wins, hs, hl, Bool.false_eq_true] at hwin
  | ok left =>
    cases hr : checked.right with
    | error cause => simp only [wins, hs, hl, hr, Bool.false_eq_true] at hwin
    | ok right =>
      have hw : left.hashes.lines = right.hashes.lines ∧ ∃ (e : Fin tau) (i : Fin N) (ls rs : Seed lambda),
          left.reconstruction.seeds e i = some ls ∧ right.reconstruction.seeds e i = some rs ∧ ls ≠ rs := by
        simpa only [wins, hs, hl, hr, decide_eq_true_eq] using hwin
      obtain ⟨e, i, ls, rs, hls, hrs, hne⟩ := hw.2
      exact ⟨checked.claim, left, right, e, i, ls, rs, by simpa only [hl] using he.2.1,
        by simpa only [hr] using he.2.2, hw.1, hls, hrs, hne⟩

/-- Transfer of the joint pipeline bound at this program boundary. The
coverage argument is discharged below for the full and Category-III layouts. -/
theorem event_bound {Tag : Type*} (layout : Layout lambda Key Block) (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N Key Block Context Error)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity)
    (hcover : ∀ joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N p m)
      (fun state => verifyProgram layout variant Topen (choose state))).support, wins joint.2 = true →
        (∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView joint.2) = true) ∨
          Spec.IdealCipherPairCollision.Witnessed project companion joint.1 joint.2.cipherHistory) :
    ((experiment layout variant Topen p m adversary q initial choose).map wins) true ≤
      ((q + verificationBudget tau N p m).choose 2 : ℝ≥0∞) *
        ((Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ +
          IdealCipherPairAdaptive.pairCost Block capacity (q + verificationBudget tau N p m)) :=
  HashCipherPipelineSecurity.event_bound adversary q initial procedure (verificationBudget tau N p m)
    (fun state => verifyProgram layout variant Topen (choose state)) project companion hinvolution hnofix capacity hcapacity wins hcover

theorem full_winning_covered (hlambda : 26 ≤ lambda) (hcount : 4 * (tau * N) ≤ 2 ^ 24)
    (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N (Bits lambda) (Bits lambda) Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right)
    (joint : Spec.IdealCipher.Family (Bits lambda) (Bits lambda) ×
      Spec.HashCipher.Result (List Bool) (Digest lambda) (Bits lambda) (Bits lambda)
        (ChainProgram lambda (Bits lambda) (Bits lambda) (Checked lambda tau N (Bits lambda) (Bits lambda) Context Error)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N p m)
      (fun state => verifyProgram (fullLayout lambda) variant Topen (choose state))).support)
    (hwin : wins joint.2 = true) :
    (∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView joint.2) = true) ∨
      Spec.IdealCipherPairCollision.Witnessed id Spec.SeedPairing.companion joint.1 joint.2.cipherHistory := by
  obtain ⟨claim, left, right, e, i, ls, rs, hl, hr, hlines, hls, hrs, hne⟩ :=
    winning_evaluations (fullLayout lambda) variant Topen p m adversary q initial choose hbounds joint hout hwin
  rcases evaluated_collision (fullLayout lambda) variant Topen claim joint.1 joint.2
    left right hl hr hlines e i ls rs hls hrs hne with hh | ⟨_, hseed, hcalls⟩
  · exact Or.inl hh
  · exact Or.inr (SeedPairBinding.full_seed_collision_witnessed hlambda hcount (SeedTree.leafOffset_lt e i)
      variant joint.1 claim.left.opening.salt ls rs joint.2.cipherHistory hseed.1 hseed.2 (hcalls false).1 (hcalls false).2)

theorem truncated_winning_covered (hcount : 4 * (tau * N) ≤ 2 ^ 24) (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest 192) (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → Claim 192 tau N (Bits 256) (Bits 256) Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right)
    (joint : Spec.IdealCipher.Family (Bits 256) (Bits 256) ×
      Spec.HashCipher.Result (List Bool) (Digest 192) (Bits 256) (Bits 256)
        (ChainProgram 192 (Bits 256) (Bits 256) (Checked 192 tau N (Bits 256) (Bits 256) Context Error)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N p m)
      (fun state => verifyProgram truncatedLayout variant Topen (choose state))).support)
    (hwin : wins joint.2 = true) :
    (∃ pair, Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView joint.2) = true) ∨
      Spec.IdealCipherPairCollision.Witnessed Spec.IdealCipherSeed.project192 Spec.SeedPairing.companion joint.1 joint.2.cipherHistory := by
  obtain ⟨claim, left, right, e, i, ls, rs, hl, hr, hlines, hls, hrs, hne⟩ :=
    winning_evaluations truncatedLayout variant Topen p m adversary q initial choose hbounds joint hout hwin
  rcases evaluated_collision truncatedLayout variant Topen claim joint.1 joint.2
    left right hl hr hlines e i ls rs hls hrs hne with hh | ⟨_, hseed, hcalls⟩
  · exact Or.inl hh
  · exact Or.inr (SeedPairBinding.truncated_seed_collision_witnessed hcount (SeedTree.leafOffset_lt e i)
      variant joint.1 claim.left.opening.salt ls rs joint.2.cipherHistory hseed.1 hseed.2 (hcalls false).1 (hcalls false).2)

/-- Q = q + 2*(reconstruction budget + p + m + 2) counts both complete
reconstructions, both supplied intermediate programs and all four chain hash
calls. The event concerns successful equal-line-digest executions only;
undefined source outcomes remain explicit error values in the game. -/
theorem full_disagreement_bound (hlambda : 26 ≤ lambda) (hcount : 4 * (tau * N) ≤ 2 ^ 24)
    (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N (Bits lambda) (Bits lambda) Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right) :
    ((experiment (fullLayout lambda) variant Topen p m adversary q initial choose).map wins) true ≤
      ((q + verificationBudget tau N p m).choose 2 : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹ ^ (2 * lambda) +
          (((2 ^ lambda - (q + verificationBudget tau N p m) : Nat) : ℝ≥0∞)⁻¹ *
            ((2 ^ lambda - (q + verificationBudget tau N p m + 2) : Nat) : ℝ≥0∞)⁻¹)) := by
  have h := event_bound (fullLayout lambda) variant Topen p m adversary q initial choose id Spec.SeedPairing.companion
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by omega)) 1 (by intro target; simp)
    (fun joint hj hw => full_winning_covered hlambda hcount variant Topen p m adversary q initial choose hbounds joint hj hw)
  simpa only [Digest, Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow, IdealCipherPairAdaptive.pairCost, Nat.cast_one, one_div] using h

theorem truncated_disagreement_bound (hcount : 4 * (tau * N) ≤ 2 ^ 24) (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest 192) (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → Claim 192 tau N (Bits 256) (Bits 256) Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right) :
    ((experiment truncatedLayout variant Topen p m adversary q initial choose).map wins) true ≤
      ((q + verificationBudget tau N p m).choose 2 : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹ ^ 384 +
          (((2 : ℝ≥0∞) ^ 64 / ((2 ^ 256 - (q + verificationBudget tau N p m) : Nat) : ℝ≥0∞)) *
            ((2 : ℝ≥0∞) ^ 64 / ((2 ^ 256 - (q + verificationBudget tau N p m + 2) : Nat) : ℝ≥0∞)))) := by
  have h := event_bound truncatedLayout variant Topen p m adversary q initial choose Spec.IdealCipherSeed.project192 Spec.SeedPairing.companion
    SeedPairing.companion_involutive (SeedPairing.companion_ne (by decide : 0 < 256)) (2 ^ 64)
    (fun target => IdealCipherSeed.project192_fiber_card target _)
    (fun joint hj hw => truncated_winning_covered hcount variant Topen p m adversary q initial choose hbounds joint hj hw)
  apply h.trans
  apply le_of_eq
  simp only [Digest, Bits, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow, IdealCipherPairAdaptive.pairCost]

end
end SDitH.Proofs.BLCReconstructionChain
