import SDitH.Proofs.CipherInvariant
import SDitH.Proofs.CandidatePrune
import SDitH.Proofs.ForkRestore
import SDitH.Proofs.TraceGrowth

/-! Two further facts about the extended counted invariant: it is kept by
restoring a final world's family and history into a snapshot's world, and
by the verification preparation when the verification budget is at most
the commitment budget. -/

namespace SDitH.Proofs.InvCExtra

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open CipherResample GameResample ChargeExpect SharedResample CandidateResample CandidatePrepLaw
open GamePrune PruneLawRun CandidatePrune ForkRestore CipherInvariant SimulationGapTrace SharedGameInvariant TraceGrowth
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The extended invariant is kept by restoring a final world's family and
history into a snapshot's world. -/
theorem invC_restore (n : Nat)
    (W wL : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hW : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n W)
    (hL : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n wL) :
    InvC (tau := tau) (kappa := kappa) n (restore W wL) :=
  ⟨⟨hW.1.1, hW.1.2.1, hW.1.2.2⟩, hL.2.1, hL.2.2⟩

/-- The verification preparation keeps the extended invariant when the
verification budget is at most the commitment budget. -/
theorem invC_prep (hvc : verifyBudget ≤ commitBudget tau kappa) (pk message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (n : Nat) (r)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world)
    (hr : r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification
      pk message signature world).support) :
    InvC (tau := tau) (kappa := kappa) (n + 1) r.2 := by
  rcases signature with ⟨piop, _ | body⟩
  · rw [prepareVerification_none_eq] at hr
    simp only [PMF.mem_support_pure_iff] at hr
    subst hr
    exact invC_mono n (n + 1) world (Nat.le_succ n) h
  · rw [prepareVerification_some_eq] at hr
    simp only [runOracle, PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hr
    obtain ⟨res, hres, q, rfl, rfl⟩ := hr
    have hc := runProgram_cipher _ _ world.other res hres h.2.1
    have ht := runProgram_trace_le _ _ world.other res hres
    have hwf := runProgram_wellFormed _ _ world.other res hres h.1.2.1
    have h3 := h.1.2.2
    have h4 := h.2.2
    refine ⟨⟨TableSupport.supported_mono h.1.1 (Nat.le_succ n), hwf, ?_⟩, hc.1, ?_⟩
    · calc res.2.trace.length ≤ world.other.trace.length + verifyBudget := ht
        _ ≤ commitBudget tau kappa * n + commitBudget tau kappa := by omega
        _ = commitBudget tau kappa * (n + 1) := by ring
    · calc res.2.cipherHistory.length ≤ world.other.cipherHistory.length + verifyBudget := hc.2
        _ ≤ commitBudget tau kappa * n + commitBudget tau kappa := by omega
        _ = commitBudget tau kappa * (n + 1) := by ring

end
end SDitH.Proofs.InvCExtra
