import SDitH.Spec.CandidateVerifier
import SDitH.Proofs.BLCSeedLines
import SDitH.Proofs.HashCipherEvaluation

/-! The literal fold with the reconstruction's revealed seeds agrees with
the fold of any complete seed vector agreeing with them: the hidden index
is never read. Hence the candidate middle's share matrix is the affine
share matrix of that vector, and its candidate base is the masked slope
times the hidden Gray row plus the intercept's columns minus the plain
term. These are deterministic identities about the named candidate. -/

namespace SDitH.Proofs.CandidateVerifier

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.BLCRecompute Spec.CandidateVerifier
open Spec.BLCSeedFold Spec.BLCSeedLines Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.SlopeConsistencyGame (Out)
open scoped Classical BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The leaf fold reads only non-hidden seeds, so a partial array agreeing
with a complete vector there gives the complete vector's prefix sums. -/
theorem foldLeaves_sum_partial (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (values : SeedArray lambda tau kappa) (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (e : Fin tau)
    (hidden : Fin (2 ^ kappa)) (hagree : ∀ i, i ≠ hidden → values e i = some (full e i))
    (initial : Share (s + (wit + rnd)) kappa) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (count : Nat) (hc : count ≤ 2 ^ kappa) :
    foldLeavesThrough p salt (some values) e hidden (some initial) randomCount enough count hc =
      .ok (some fun c j => initial c j +
        BLCRecompute.prefixSum (Spec.BLCCommit.randomTable p salt full randomCount enough e) hidden count c j) := by
  induction count with
  | zero => simp [foldLeavesThrough, BLCRecompute.prefixSum]
  | succ count ih =>
    simp only [foldLeavesThrough, ih (by omega), Bind.bind, Except.bind]
    split
    · rename_i he
      congr 2
      funext c j
      rw [BLCRecompute.prefixSum_succ _ _ _ (by omega), he]
      simp
    · rename_i hne
      rw [readSeed, hagree ⟨count, by omega⟩ hne]
      simp only [addShare]
      congr 2
      funext c j
      rw [BLCRecompute.prefixSum_succ _ _ _ (by omega)]
      change initial c j + BLCRecompute.prefixSum _ _ count c j + _ = initial c j + (BLCRecompute.prefixSum _ _ count c j + _)
      exact add_assoc _ _ _

theorem foldExecution_reconstruction (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (nodes : NodesBinding lambda tau (2 ^ kappa)) (recon : Reconstructed lambda tau (2 ^ kappa))
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau)
    (hagree : ∀ i, i ≠ hidden e → recon.seeds e i = some (full e i)) :
    foldExecution p salt (reconstructionBindings nodes recon) aux hidden randomCount enough e =
      .ok ⟨0, some fun c j => affine p salt full randomCount enough aux e (hidden e) c j⟩ := by
  have hfold := foldLeaves_sum_partial p salt recon.seeds full e (hidden e) hagree 0 randomCount enough (2 ^ kappa) le_rfl
  have hext := BLCSeedFold.foldExecution_extracted p salt nodes full aux hidden randomCount enough e
  rw [extractedBindings] at hext
  simp only [foldExecution, reconstructionBindings, hfold, Bind.bind, Except.bind]
  simp only [foldExecution, BLCRecompute.foldLeaves_sum, Bind.bind, Except.bind] at hext
  exact hext

theorem foldExecutions_reconstruction (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (nodes : NodesBinding lambda tau (2 ^ kappa)) (recon : Reconstructed lambda tau (2 ^ kappa))
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (hagree : ∀ e i, i ≠ hidden e → recon.seeds e i = some (full e i))
    (folded : Vector (FoldedExecution (s + (wit + rnd)) kappa) tau)
    (hfold : foldExecutionsThrough p salt (reconstructionBindings nodes recon) aux hidden randomCount enough tau le_rfl = .ok folded)
    (shares : Vector (Share (s + (wit + rnd)) kappa) tau) (hshares : collectShares folded = .ok shares) :
    concatenate shares = shareMatrix p salt full randomCount enough aux hidden := by
  funext c e j
  have hrow := BLCRecompute.foldExecutions_coordinate p salt (reconstructionBindings nodes recon) aux hidden
    randomCount enough tau le_rfl folded hfold e.val e.isLt
  rw [foldExecution_reconstruction p salt nodes recon full aux hidden randomCount enough ⟨e.val, e.isLt⟩
    (hagree ⟨e.val, e.isLt⟩)] at hrow
  have hshare := BLCRecompute.collectShares_coordinate folded shares hshares e.val e.isLt
  have hval : folded[e.val] = ⟨0, some fun c j =>
      affine p salt full randomCount enough aux ⟨e.val, e.isLt⟩ (hidden ⟨e.val, e.isLt⟩) c j⟩ :=
    (Except.ok.inj hrow).symm
  rw [hval] at hshare
  have hfin : (⟨e.val, e.isLt⟩ : Fin tau) = e := Fin.eta e e.isLt
  simp only [hfin] at hshare
  have hs := Option.some.inj hshare
  show shares[e.val] c j = _
  rw [← hs]
  rfl

/-- A successful candidate-middle evaluation records the mask lookup and
returns the affine share matrix's candidate base and the suffix values. -/
theorem candidateMiddle_evaluates {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (nodes : NodesBinding lambda tau (2 ^ kappa))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (hidden : Fin tau → Fin (2 ^ kappa))
    (recon : Reconstructed lambda tau (2 ^ kappa)) (auxiliary : Digest lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (hagree : ∀ e i, i ≠ hidden e → recon.seeds e i = some (full e i))
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (value : F × (Fin wit → F) × (Fin rnd → F) × (Fin s → Fin tau → Fin kappa → ZMod 2))
    (h : Evaluates family table ciphers
      (candidateMiddle xi p nodes encode randomCount enough salt aux hidden recon auxiliary) (Except.ok value)) :
    ∃ pm, table (maskInput auxiliary) = some pm ∧
      value.1 = (encode hidden)⁻¹ ∧
      (∀ j, value.2.1 j = algebraMap (ZMod 2) F (aux.witnessCorrection j) +
        (encode hidden)⁻¹ * Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.witnessIndex j))) ∧
      (∀ j, value.2.2.1 j =
        (encode hidden)⁻¹ * Spec.BLC.psi xi (shareMatrix p salt full randomCount enough aux hidden (Spec.BLC.randomnessIndex j))) ∧
      value.2.2.2 = candidateBase pm.2 aux.plain hidden (shareMatrix p salt full randomCount enough aux hidden) := by
  unfold candidateMiddle at h
  cases h with
  | hash _ _ pm _ hpm tail =>
    refine ⟨pm, hpm, ?_⟩
    split at tail
    · cases tail
    · rename_i folded hfold
      split at tail
      · cases tail
      · rename_i shares hshares
        cases tail
        have hQ := foldExecutions_reconstruction p salt nodes recon full aux hidden randomCount enough hagree folded hfold shares hshares
        simp only [hQ]
        exact ⟨trivial, fun _ => trivial, fun _ => trivial, trivial⟩

/-- The candidate base in terms of the masked slope and the intercept's columns. -/
theorem candidateBase_affine (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (hidden : Fin tau → Fin (2 ^ kappa))
    (a : Fin s) (e : Fin tau) (j : Fin kappa) :
    candidateBase M aux.plain hidden (shareMatrix p salt full randomCount enough aux hidden) a e j =
      (maskedSlope p salt full randomCount enough aux M e a - aux.plain a) * Spec.GrayCode.grayFieldRow (hidden e) j +
        Spec.BLC.consistencyColumns M (interceptMatrix p salt full randomCount enough) a e j := by
  rw [candidateBase, BLCSeedLines.consistencyColumns_affine]
  ring

end
end SDitH.Proofs.CandidateVerifier
