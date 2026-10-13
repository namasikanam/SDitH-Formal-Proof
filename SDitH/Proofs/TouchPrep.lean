import SDitH.Proofs.SwapDischarge
import SDitH.Proofs.CommitPhaseExchange

/-! Preparations for the touching bound's instantiation. The simulated
post-processing reads the committed key only through the candidate
opening, which reveals the leaves other than the hidden ones and the
commitments, so setting an internal node of the committed tree leaves it
unchanged; the signing-shaped oracle with the simulated post-processing is
one branch of the simulated signing, so it keeps the extended invariant;
and pruning keeps the extended invariant. -/

namespace SDitH.Proofs.TouchPrep

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator Spec.BLC
open Spec.SharedSigner (commitBudget Committed)
open Spec.BAVC (Digest)
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher (Family Entry)
open CandidateResample CipherInvariant HiddenEntries GamePrune SignBridge SwapDischarge CommitPhaseExchange SharedPrune
open GameResample CipherResample
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A leaf's address is at least the leaf count. -/
theorem leafCount_le_leafAddress (e : Fin tau) (i : Fin (2 ^ kappa)) :
    tau * 2 ^ kappa ≤ Spec.SeedTree.leafAddress e i :=
  Nat.le_add_right _ _

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The candidate opening does not read an internal node of the key's tree. -/
theorem openKey_setTree (b : Nat) (hb : b < tau * 2 ^ kappa) (key : Spec.BAVC.Key lambda tau (2 ^ kappa))
    (x : Spec.BAVC.Seed lambda) (hidden : Fin tau → Fin (2 ^ kappa)) :
    Spec.CandidateBAVC.openKey { key with tree := fun a => if a.val = b then x else key.tree a } hidden =
      Spec.CandidateBAVC.openKey key hidden := by
  unfold Spec.CandidateBAVC.openKey
  refine congrArg₂ _ (funext fun e => funext fun i => ?_) rfl
  by_cases hi : i = hidden e
  · simp [hi]
  · have hne : (Spec.BAVC.leafNode e i).val ≠ b := by
      have := leafCount_le_leafAddress e i
      show Spec.SeedTree.leafAddress e i ≠ b
      omega
    simp [hi, hne]

omit [NeZero tau] in
/-- The simulated post-processing is invariant under setting an internal
node of the committed tree. -/
theorem simPost_setTree (pk message : List Bool) (salt : Bits lambda) (digest : Digest lambda) (b : Nat)
    (hb : b < tau * 2 ^ kappa) (x : Spec.BAVC.Seed lambda)
    (c : Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (table : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda)) :
    simPost S pk message salt digest (.done (setTree b x c)) table = simPost S pk message salt digest (.done c) table := by
  have hatt : ∀ ctr, attempt (stateOf S salt (setTree b x c)).2.key (S.expandEvaluation digest) S.encode ctr =
      attempt (stateOf S salt c).2.key (S.expandEvaluation digest) S.encode ctr := by
    intro ctr
    simp only [attempt, stateOf, setTree]
    split_ifs
    · rw [openKey_setTree b hb]
    · rfl
  have hobs : Spec.BLCRetry.observe (attempt (stateOf S salt (setTree b x c)).2.key (S.expandEvaluation digest) S.encode) S.fuel 0 =
      Spec.BLCRetry.observe (attempt (stateOf S salt c).2.key (S.expandEvaluation digest) S.encode) S.fuel 0 := by
    congr 1
    funext ctr
    exact hatt ctr
  simp only [simPost]
  rw [hobs]
  rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- Pruning keeps the extended invariant. -/
theorem invC_pruneW (K : List (Bits lambda)) (n : Nat)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) :
    InvC (tau := tau) (kappa := kappa) n (pruneW K world) :=
  ⟨h.1, matches_pruneAt K _ _ h.2.1, le_trans (List.length_filter_le _ _) h.2.2⟩

include V verifyBudget sampleWitness in
/-- The signing-shaped oracle with the simulated post-processing keeps the
extended invariant: it is one branch of the simulated signing. -/
theorem invC_commitOracle (salt root : Bits lambda) (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (digest : Digest lambda) (n : Nat)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) (r)
    (hr : r ∈ (commitOracle S.signer salt wsign root (simPost S publicKey message salt digest) world).support) :
    InvC (tau := tau) (kappa := kappa) (n + 1) r.2 := by
  refine invC_simulated S V verifyBudget publicKey sampleWitness (publicKey, wsign) message world n r h ?_
  rw [simulated_sign_shape]
  unfold commitOracle at hr
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_uniformOfFintype, true_and] at hr ⊢
  exact ⟨salt, root, wsign, digest, hr⟩

end
end SDitH.Proofs.TouchPrep
