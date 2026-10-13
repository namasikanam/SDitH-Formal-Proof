import SDitH.Spec.BLCSeedExtraction
import SDitH.Proofs.BLCReconstructionChain

/-! Two successful chain executions with different hidden indices at an
execution e reveal, between them, every leaf of e. If their commonly revealed
seeds agree, the pointwise merge is the unique complete vector agreeing with
both. Failure of this extraction therefore implies the already bounded
disagreement event. No witness, challenge or signature claim is made. -/

namespace SDitH.Proofs.BLCSeedExtraction

open Spec.DomainSeparation Spec.BAVC Spec.BAVCCipherProgram Spec.BAVCReconstructionProgram
open Spec.BLCHashChain Spec.BLCReconstructionChain Spec.BLCSeedExtraction
open Spec.HashCipherProgram Spec.HashCipherEvaluation
open scoped Classical ENNReal
noncomputable section

variable {lambda tau N : Nat} {Key Block Context Error State : Type*}

theorem reconstructed_revealed_present (p : Primitives lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initial : NodesBinding lambda tau N) (out : Reconstructed lambda tau N)
    (h : reconstructWithNodes p salt hidden opening Topen initial = .ok out) (e : Fin tau) (i : Fin N)
    (hi : i ≠ hidden e) : ∃ seed, out.seeds e i = some seed := by
  obtain ⟨_, nodes, rows, _, _, hr, rfl⟩ :=
    (BAVCReconstruction.reconstructWithNodes_ok_iff p salt hidden opening Topen initial out).mp h
  obtain ⟨seed, _, hrow⟩ := BAVCReconstruction.successful_rows_revealed p salt hidden opening nodes rows hr e i hi
  exact ⟨seed, by show (rows[e][i]).seed = some seed; rw [hrow]⟩

theorem merge_agrees (left right : Reconstructed lambda tau N) (e : Fin tau)
    (hcons : Consistent left right e) : Agrees left right e (merge left right e) := by
  constructor
  · intro i s hs
    simp only [merge, hs]
  · intro i s hs
    cases hl : left.seeds e i with
    | none => simp only [merge, hl, hs]
    | some ls =>
      simp only [merge, hl]
      exact hcons i ls s hl hs

/-- Differing hidden indices mean every leaf of e is revealed by one side,
so an agreeing complete vector is unique and equals the merge. -/
theorem unique_agreeing (p p' : Primitives lambda) (saltL saltR : Seed lambda)
    (hiddenL hiddenR : Fin tau → Fin N) (openingL openingR : Opening lambda tau) (Topen : Nat)
    (nodesL nodesR : NodesBinding lambda tau N) (left right : Reconstructed lambda tau N)
    (hl : reconstructWithNodes p saltL hiddenL openingL Topen nodesL = .ok left)
    (hr : reconstructWithNodes p' saltR hiddenR openingR Topen nodesR = .ok right)
    (e : Fin tau) (hne : hiddenL e ≠ hiddenR e) (hcons : Consistent left right e) :
    Agrees left right e (merge left right e) ∧
      ∀ other, Agrees left right e other → other = merge left right e := by
  have hmerge := merge_agrees left right e hcons
  refine ⟨hmerge, fun other hother => funext fun i => ?_⟩
  by_cases hi : i = hiddenL e
  · have hi' : i ≠ hiddenR e := by rw [hi]; exact hne
    obtain ⟨s, hs⟩ := reconstructed_revealed_present p' saltR hiddenR openingR Topen nodesR right hr e i hi'
    rw [hother.2 i s hs, hmerge.2 i s hs]
  · obtain ⟨s, hs⟩ := reconstructed_revealed_present p saltL hiddenL openingL Topen nodesL left hl e i hi
    rw [hother.1 i s hs, hmerge.1 i s hs]

variable [Fintype Key] [Fintype Block]

/-- On the game's support, extraction failure is a disagreement. The
reconstruction facts come from the actual evaluations, not from a contract. -/
theorem fails_implies_wins (layout : Layout lambda Key Block) (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N Key Block Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right)
    (joint : Spec.IdealCipher.Family Key Block × Spec.HashCipher.Result (List Bool) (Digest lambda) Key Block
      (ChainProgram lambda Key Block (Checked lambda tau N Key Block Context Error)))
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment adversary q initial procedure (verificationBudget tau N p m)
      (fun state => verifyProgram layout variant Topen (choose state))).support)
    (hfail : extractionFails joint.2 = true) : wins joint.2 = true := by
  obtain ⟨checked, hs, hv⟩ := BLCReconstructionChain.joint_complete layout variant Topen p m adversary q initial choose hbounds joint hout
  have he := BLCReconstructionChain.verify_evaluates layout variant Topen checked.claim joint.1 joint.2.hashTable joint.2.cipherHistory checked hv
  cases hl : checked.left with
  | error cause => simp only [extractionFails, hs, hl, Bool.false_eq_true] at hfail
  | ok left =>
    cases hr : checked.right with
    | error cause => simp only [extractionFails, hs, hl, hr, Bool.false_eq_true] at hfail
    | ok right =>
      have hf : left.hashes.lines = right.hashes.lines ∧
          ∃ e : Fin tau, checked.claim.left.opening.hidden e ≠ checked.claim.right.opening.hidden e ∧
            ¬ ∃ full : Fin N → Seed lambda, Agrees left.reconstruction right.reconstruction e full ∧
              ∀ other, Agrees left.reconstruction right.reconstruction e other → other = full := by
        simpa only [extractionFails, hs, hl, hr, decide_eq_true_eq] using hfail
      obtain ⟨e, hne, hnone⟩ := hf.2
      have hlr := (BLCReconstructionChain.open_evaluates layout variant Topen checked.claim.left joint.1
        joint.2.hashTable joint.2.cipherHistory left (by simpa only [hl] using he.2.1)).1
      have hrr := (BLCReconstructionChain.open_evaluates layout variant Topen checked.claim.right joint.1
        joint.2.hashTable joint.2.cipherHistory right (by simpa only [hr] using he.2.2)).1
      have hlrec := (BAVCReconstructionProgram.reconstruction_evaluates layout variant joint.1 joint.2.hashTable
        joint.2.cipherHistory _ _ _ Topen _ _ hlr).1
      have hrrec := (BAVCReconstructionProgram.reconstruction_evaluates layout variant joint.1 joint.2.hashTable
        joint.2.cipherHistory _ _ _ Topen _ _ hrr).1
      have hinc : ¬ Consistent left.reconstruction right.reconstruction e := by
        intro hcons
        exact hnone ⟨_, unique_agreeing _ _ _ _ _ _ _ _ Topen _ _ _ _ hlrec hrrec e hne hcons⟩
      simp only [Consistent] at hinc
      push_neg at hinc
      obtain ⟨i, ls, rs, hls, hrs, hne'⟩ := hinc
      simp only [wins, hs, hl, hr, decide_eq_true_eq]
      exact ⟨hf.1, e, i, ls, rs, hls, hrs, hne'⟩

theorem failure_le_disagreement (layout : Layout lambda Key Block) (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) Key Block State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N Key Block Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right) :
    ((experiment layout variant Topen p m adversary q initial choose).map extractionFails) true ≤
      ((experiment layout variant Topen p m adversary q initial choose).map wins) true := by
  unfold Spec.BLCReconstructionChain.experiment
  simp only [Spec.HashCipherPipeline.experiment, PMF.map_comp, Function.comp_def]
  apply HashCipherPipelineSecurity.event_mass_le
  intro joint hs hf
  exact fails_implies_wins layout variant Topen p m adversary q initial choose hbounds joint hs hf

/-- Seed-vector extraction fails with at most the chain disagreement
probability. Q = q + 2*(B + p + m + 2) as in the chain bound. -/
theorem full_failure_bound (hlambda : 26 ≤ lambda) (hcount : 4 * (tau * N) ≤ 2 ^ 24)
    (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest lambda) (Bits lambda) (Bits lambda) State)
    (q : Nat) (initial : State) (choose : State → Claim lambda tau N (Bits lambda) (Bits lambda) Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right) :
    ((experiment (fullLayout lambda) variant Topen p m adversary q initial choose).map extractionFails) true ≤
      ((q + verificationBudget tau N p m).choose 2 : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹ ^ (2 * lambda) +
          (((2 ^ lambda - (q + verificationBudget tau N p m) : Nat) : ℝ≥0∞)⁻¹ *
            ((2 ^ lambda - (q + verificationBudget tau N p m + 2) : Nat) : ℝ≥0∞)⁻¹)) :=
  (failure_le_disagreement (fullLayout lambda) variant Topen p m adversary q initial choose hbounds).trans
    (BLCReconstructionChain.full_disagreement_bound hlambda hcount variant Topen p m adversary q initial choose hbounds)

theorem truncated_failure_bound (hcount : 4 * (tau * N) ≤ 2 ^ 24) (variant : Grinding) (Topen p m : Nat)
    (adversary : Spec.HashCipher.Procedure (List Bool) (Digest 192) (Bits 256) (Bits 256) State)
    (q : Nat) (initial : State) (choose : State → Claim 192 tau N (Bits 256) (Bits 256) Context Error)
    (hbounds : ∀ state, Bounds p m (choose state).left ∧ Bounds p m (choose state).right) :
    ((experiment truncatedLayout variant Topen p m adversary q initial choose).map extractionFails) true ≤
      ((q + verificationBudget tau N p m).choose 2 : ℝ≥0∞) *
        ((2 : ℝ≥0∞)⁻¹ ^ 384 +
          (((2 : ℝ≥0∞) ^ 64 / ((2 ^ 256 - (q + verificationBudget tau N p m) : Nat) : ℝ≥0∞)) *
            ((2 : ℝ≥0∞) ^ 64 / ((2 ^ 256 - (q + verificationBudget tau N p m + 2) : Nat) : ℝ≥0∞)))) :=
  (failure_le_disagreement truncatedLayout variant Topen p m adversary q initial choose hbounds).trans
    (BLCReconstructionChain.truncated_disagreement_bound hcount variant Topen p m adversary q initial choose hbounds)

end
end SDitH.Proofs.BLCSeedExtraction
