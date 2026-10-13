import SDitH.Proofs.SharedScheme
import SDitH.Proofs.BAVCReconstructionGame
import SDitH.Proofs.BLCSeedExtraction
import SDitH.Proofs.SlopeConsistency

/-! A successful executed verification decomposes into a successful
reconstruction evaluation on the digest projection of the table, the two
chain lookups and the middle's evaluation. Two successful verifications
with equal lines digests therefore have equal roots unless two distinct
inputs share a digest; with a disagreeing commonly revealed seed they give
a digest collision or a seed collision with its cipher entries recorded;
and with hidden indices differing at an execution they determine a unique
complete seed vector for it unless such a collision occurs. -/

namespace SDitH.Proofs.SharedSchemeChain

open Spec.BAVC Spec.DomainSeparation Spec.SharedScheme Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.SlopeConsistency Spec.BLCSeedExtraction
open Spec.SlopeConsistencyGame (Out)
open scoped Classical
noncomputable section

variable {F : Type*} {lambda tau kappa s wit rnd : Nat}

/-- `of_decide_eq_true` with the decidability instance unified rather than
re-synthesized. -/
theorem of_decide_true {p : Prop} {inst : Decidable p} (h : @decide p inst = true) : p := by
  cases inst with
  | isTrue hp => exact hp
  | isFalse _ => cases h

abbrev projected (table : List Bool → Option (Out lambda s wit rnd)) : List Bool → Option (Digest lambda) :=
  fun x => (table x).map Prod.fst

theorem verify_evaluates (V : VerifierSetting F lambda tau kappa s wit rnd) (salt : Bits lambda)
    (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (piop : Digest lambda)
    (decomposition : Spec.BLCRetry.Counter × Opening lambda tau)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (recovered : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (h : Evaluates family table ciphers (verifyProgram V salt aux piop decomposition) (Except.ok recovered)) :
    ∃ (reconstruction : Reconstructed lambda tau (2 ^ kappa)) (pa pl : Out lambda s wit rnd)
      (value : F × (Fin wit → F) × (Fin rnd → F) × (Fin s → Fin tau → Fin kappa → ZMod 2)),
      Evaluates family (projected table) ciphers
        (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant salt (V.expand piop decomposition.1)
          decomposition.2 V.Topen V.nodes) (Except.ok reconstruction) ∧
      table (Spec.BLCHashChain.auxQuery reconstruction.hcom (Spec.BLCHashChain.sourceTail V.encoding aux.corrections)) = some pa ∧
      Evaluates family table ciphers (V.middle salt aux (V.expand piop decomposition.1) reconstruction pa.1) (Except.ok value) ∧
      table (Spec.BLCHashChain.linesQuery pa.1 (V.encoding.vector aux.plain ++ V.encoding.base value.2.2.2)) = some pl ∧
      recovered = ⟨value.1, value.2.1, value.2.2.1, pl.1⟩ := by
  unfold verifyProgram at h
  obtain ⟨result, hr, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp h
  cases result with
  | error cause => cases ht
  | ok reconstruction =>
    cases ht with
    | hash _ _ pa _ hpa tail =>
      obtain ⟨middle, hm, ht⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ _).mp tail
      cases middle with
      | error cause => cases ht
      | ok value =>
        cases ht with
        | hash _ _ pl _ hpl done =>
          cases done
          exact ⟨reconstruction, pa, pl, value, (SharedScheme.liftFirst_evaluates family table ciphers _ _).mp hr,
            hpa, hm, hpl, rfl⟩

/-- Two successful verifications with equal lines digests have equal roots,
unless two distinct inputs of the table share a digest component. -/
theorem equal_lines_root_or_collision (V : VerifierSetting F lambda tau kappa s wit rnd)
    (saltL saltR : Bits lambda) (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (piopL piopR : Digest lambda)
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (left right : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family table ciphers (verifyProgram V saltL auxL piopL decL) (Except.ok left))
    (hr : Evaluates family table ciphers (verifyProgram V saltR auxR piopR decR) (Except.ok right))
    (hlines : left.lines = right.lines) (hfree : DigestCollisionFree table) :
    ∃ reconL reconR : Reconstructed lambda tau (2 ^ kappa),
      Evaluates family (projected table) ciphers
        (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant saltL (V.expand piopL decL.1) decL.2 V.Topen V.nodes)
        (Except.ok reconL) ∧
      Evaluates family (projected table) ciphers
        (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant saltR (V.expand piopR decR.1) decR.2 V.Topen V.nodes)
        (Except.ok reconR) ∧
      reconL.hcom = reconR.hcom := by
  obtain ⟨reconL, paL, plL, vL, hrecL, hpaL, _, hplL, hleft⟩ := verify_evaluates V saltL auxL piopL decL family table ciphers left hl
  obtain ⟨reconR, paR, plR, vR, hrecR, hpaR, _, hplR, hright⟩ := verify_evaluates V saltR auxR piopR decR family table ciphers right hr
  refine ⟨reconL, reconR, hrecL, hrecR, ?_⟩
  have hpl : plL.1 = plR.1 := by
    have := hlines
    rw [hleft, hright] at this
    exact this
  have hlq := hfree _ _ plL plR hplL hplR hpl
  have hpa1 : paL.1 = paR.1 := Proofs.BLCHashChain.lines_header paL.1 paR.1 _ _ hlq
  have haq := hfree _ _ paL paR hpaL hpaR hpa1
  exact Proofs.BLCHashChain.aux_header reconL.hcom reconR.hcom _ _ haq

/-- The projected table viewed as a shared-model result for the existing
reconstruction collision lemma. -/
def projectedResult (table : List Bool → Option (Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) :
    Spec.HashCipher.Result (List Bool) (Digest lambda) (Bits lambda) (Bits lambda) Unit :=
  ⟨(), projected table, [], ciphers, false⟩

theorem projected_collision_free (table : List Bool → Option (Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (hfree : DigestCollisionFree table)
    (pair : List Bool × List Bool)
    (hc : Spec.RandomOracleCollision.storedCollision pair (Spec.HashCipher.hashView (projectedResult table ciphers)) = true) :
    False := by
  obtain ⟨hne, answer, hl, hr⟩ := of_decide_true hc
  obtain ⟨pl, hpl, hdl⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨pr, hpr, hdr⟩ := Option.map_eq_some_iff.mp hr
  exact hne (hfree _ _ pl pr hpl hpr (hdl.trans hdr.symm))

/-- Two successful verifications with equal lines digests and hidden indices
differing at execution e determine a unique complete seed vector for e,
unless two distinct inputs share a digest or a seed collision with recorded
cipher entries occurs. -/
theorem two_verifications_seeds (V : VerifierSetting F lambda tau kappa s wit rnd)
    (saltL saltR : Bits lambda) (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (piopL piopR : Digest lambda)
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (left right : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family table ciphers (verifyProgram V saltL auxL piopL decL) (Except.ok left))
    (hr : Evaluates family table ciphers (verifyProgram V saltR auxR piopR decR) (Except.ok right))
    (hlines : left.lines = right.lines) (hfree : DigestCollisionFree table)
    (e : Fin tau) (hne : V.expand piopL decL.1 e ≠ V.expand piopR decR.1 e) :
    (∃ (i : Fin (2 ^ kappa)) (ls rs : Seed lambda), saltL = saltR ∧
        Spec.BAVCBinding.IsSeedCollision
          (Spec.BAVCReconstructionProgram.primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family (projected table))
          saltL (Spec.SeedTree.leafOffset e i) ls rs ∧
        ∀ side : Bool,
          Spec.IdealCipher.entry (.encrypt (V.layout.key ls)
            (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
            (family (V.layout.key ls) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers ∧
          Spec.IdealCipher.entry (.encrypt (V.layout.key rs)
            (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
            (family (V.layout.key rs) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers) ∨
      ∃ reconL reconR : Reconstructed lambda tau (2 ^ kappa),
        Evaluates family (projected table) ciphers
          (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant saltL (V.expand piopL decL.1) decL.2 V.Topen V.nodes)
          (Except.ok reconL) ∧
        Evaluates family (projected table) ciphers
          (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant saltR (V.expand piopR decR.1) decR.2 V.Topen V.nodes)
          (Except.ok reconR) ∧
        reconL.hcom = reconR.hcom ∧
        Agrees reconL reconR e (merge reconL reconR e) ∧
        ∀ other, Agrees reconL reconR e other → other = merge reconL reconR e := by
  obtain ⟨reconL, reconR, hrecL, hrecR, hroot⟩ :=
    equal_lines_root_or_collision V saltL saltR auxL auxR piopL piopR decL decR family table ciphers left right hl hr hlines hfree
  let claim : Spec.BAVCReconstructionGame.Claim lambda tau (2 ^ kappa) :=
    ⟨⟨saltL, V.expand piopL decL.1, decL.2, V.nodes⟩, ⟨saltR, V.expand piopR decR.1, decR.2, V.nodes⟩⟩
  by_cases hcons : Consistent reconL reconR e
  · right
    have hpureL := (BAVCReconstructionProgram.reconstruction_evaluates V.layout V.variant family (projected table) ciphers
      saltL (V.expand piopL decL.1) decL.2 V.Topen V.nodes _ hrecL).1
    have hpureR := (BAVCReconstructionProgram.reconstruction_evaluates V.layout V.variant family (projected table) ciphers
      saltR (V.expand piopR decR.1) decR.2 V.Topen V.nodes _ hrecR).1
    obtain ⟨hmerge, huniq⟩ := BLCSeedExtraction.unique_agreeing _ _ saltL saltR _ _ decL.2 decR.2 V.Topen V.nodes V.nodes
      reconL reconR hpureL hpureR e hne hcons
    exact ⟨reconL, reconR, hrecL, hrecR, hroot, hmerge, huniq⟩
  · left
    simp only [Consistent] at hcons
    push_neg at hcons
    obtain ⟨i, ls, rs, hls, hrs, hne'⟩ := hcons
    rcases BAVCReconstructionGame.evaluated_collision V.layout V.variant V.Topen claim family (projectedResult table ciphers)
      reconL reconR hrecL hrecR hroot e i ls rs hls hrs hne' with ⟨pair, hpair⟩ | ⟨hsalt, hseed, hcalls⟩
    · exact absurd hpair (projected_collision_free table ciphers hfree pair)
    · exact ⟨i, ls, rs, hsalt, hseed, hcalls⟩

end
end SDitH.Proofs.SharedSchemeChain
