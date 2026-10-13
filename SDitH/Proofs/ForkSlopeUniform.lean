import SDitH.Proofs.ForkSlope

/-! The fork-to-slope lemma with the data shared across executions made
explicit. Two candidate-middle verifications of a fork on one
collision-free table determine the two reconstructions, the common
auxiliary digest and the mask stored at it; at every execution where the
hidden indices differ, either a recorded seed collision occurs there, or
the masked slope of the merge completion of the two reconstructions, at
that stored mask, equals the plain check. The mask and the completion are
the same for all executions, which the per-execution form left implicit. -/

namespace SDitH.Proofs.ForkSlopeUniform

open Spec.BAVC Spec.DomainSeparation Spec.SharedScheme Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.SlopeConsistency Spec.BLCSeedExtraction Spec.CandidateVerifier Spec.BLCSeedLines Spec.BLCSeedFold
open Spec.SlopeConsistencyGame (Out)
open scoped Classical BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

theorem fork_masked_slope_uniform {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (V : VerifierSetting F lambda tau kappa s wit rnd)
    (hmid : V.middle = candidateMiddle xi p V.nodes encode randomCount enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (saltL saltR : Bits lambda) (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (piopL piopR : Digest lambda)
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (left right : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family table ciphers (verifyProgram V saltL auxL piopL decL) (Except.ok left))
    (hr : Evaluates family table ciphers (verifyProgram V saltR auxR piopR decR) (Except.ok right))
    (hlines : left.lines = right.lines) (hfree : DigestCollisionFree table) :
    ∃ (reconL reconR : Reconstructed lambda tau (2 ^ kappa)) (auxD : Digest lambda) (pm : Out lambda s wit rnd),
      saltL = saltR ∧ auxL.corrections = auxR.corrections ∧ auxL.plain = auxR.plain ∧
      Evaluates family (SharedSchemeChain.projected table) ciphers
        (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant saltL (V.expand piopL decL.1) decL.2 V.Topen V.nodes)
        (Except.ok reconL) ∧
      Evaluates family (SharedSchemeChain.projected table) ciphers
        (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant saltR (V.expand piopR decR.1) decR.2 V.Topen V.nodes)
        (Except.ok reconR) ∧
      table (Spec.BAVCChainInputs.maskInput auxD) = some pm ∧
      ∀ e : Fin tau, V.expand piopL decL.1 e ≠ V.expand piopR decR.1 e →
        (∃ (i : Fin (2 ^ kappa)) (ls rs : Seed lambda),
            Spec.BAVCBinding.IsSeedCollision
              (Spec.BAVCReconstructionProgram.primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family
                (SharedSchemeChain.projected table))
              saltL (Spec.SeedTree.leafOffset e i) ls rs ∧
            ∀ side : Bool,
              Spec.IdealCipher.entry (.encrypt (V.layout.key ls)
                (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
                (family (V.layout.key ls) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers ∧
              Spec.IdealCipher.entry (.encrypt (V.layout.key rs)
                (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
                (family (V.layout.key rs) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers) ∨
          ∀ a, maskedSlope p saltL (fun e' i => merge reconL reconR e' i) randomCount enough auxL pm.2 e a = auxL.plain a := by
  obtain ⟨reconL, paL, plL, valueL, hrecL, hpaL, hmidL, hplL, hleft⟩ :=
    SharedSchemeChain.verify_evaluates V saltL auxL piopL decL family table ciphers left hl
  obtain ⟨reconR, paR, plR, valueR, hrecR, hpaR, hmidR, hplR, hright⟩ :=
    SharedSchemeChain.verify_evaluates V saltR auxR piopR decR family table ciphers right hr
  have hpl : plL.1 = plR.1 := by
    have := hlines
    rw [hleft, hright] at this
    exact this
  have hlq := hfree _ _ plL plR hplL hplR hpl
  have hpa1 : paL.1 = paR.1 := Proofs.BLCHashChain.lines_header paL.1 paR.1 _ _ hlq
  have htails : V.encoding.vector auxL.plain ++ V.encoding.base valueL.2.2.2 =
      V.encoding.vector auxR.plain ++ V.encoding.base valueR.2.2.2 := by
    have he := List.append_cancel_left hlq
    exact (List.append_inj he (by simp)).2
  obtain ⟨hplain, hbase⟩ := hlinesEnc _ _ _ _ htails
  have haq := hfree _ _ paL paR hpaL hpaR hpa1
  have hroot : reconL.hcom = reconR.hcom := Proofs.BLCHashChain.aux_header reconL.hcom reconR.hcom _ _ haq
  have hcorr : auxL.corrections = auxR.corrections := by
    have he := List.append_cancel_left haq
    exact hencoding (List.append_inj he (by simp)).2
  have hsalt : saltL = saltR := ForkSlope.salt_eq_of_hcom_eq V.layout V.variant V.Topen V.nodes family table hfree ciphers
    saltL saltR _ _ decL.2 decR.2 reconL reconR hrecL hrecR hroot
  -- The completions and the candidate middle's evaluations, uniform in the execution.
  let fullL : Fin tau → Fin (2 ^ kappa) → Bits lambda := fun e' i => merge reconL reconR e' i
  let fullR : Fin tau → Fin (2 ^ kappa) → Bits lambda := fun e' i => merge reconR reconL e' i
  have hpureL := (BAVCReconstructionProgram.reconstruction_evaluates V.layout V.variant family _ ciphers
    saltL _ decL.2 V.Topen V.nodes _ hrecL).1
  have hpureR := (BAVCReconstructionProgram.reconstruction_evaluates V.layout V.variant family _ ciphers
    saltR _ decR.2 V.Topen V.nodes _ hrecR).1
  have hagreeL : ∀ e' i, i ≠ V.expand piopL decL.1 e' → reconL.seeds e' i = some (fullL e' i) := by
    intro e' i hi
    obtain ⟨seed, hseed⟩ := BLCSeedExtraction.reconstructed_revealed_present _ saltL _ decL.2 V.Topen V.nodes reconL
      hpureL e' i hi
    rw [hseed]
    simp only [fullL, ForkSlope.merge_left_revealed reconL reconR e' i seed hseed]
  have hagreeR : ∀ e' i, i ≠ V.expand piopR decR.1 e' → reconR.seeds e' i = some (fullR e' i) := by
    intro e' i hi
    obtain ⟨seed, hseed⟩ := BLCSeedExtraction.reconstructed_revealed_present _ saltR _ decR.2 V.Topen V.nodes reconR
      hpureR e' i hi
    rw [hseed]
    simp only [fullR, ForkSlope.merge_left_revealed reconR reconL e' i seed hseed]
  rw [hmid] at hmidL hmidR
  obtain ⟨pmL, hpmL, _, _, _, hbaseL⟩ := CandidateVerifier.candidateMiddle_evaluates xi p V.nodes encode randomCount enough
    saltL auxL _ reconL paL.1 fullL hagreeL family table ciphers valueL hmidL
  obtain ⟨pmR, hpmR, _, _, _, hbaseR⟩ := CandidateVerifier.candidateMiddle_evaluates xi p V.nodes encode randomCount enough
    saltR auxR _ reconR paR.1 fullR hagreeR family table ciphers valueR hmidR
  have hpm : pmL = pmR := by
    rw [hpa1] at hpmL
    exact Option.some.inj (hpmL.symm.trans hpmR)
  refine ⟨reconL, reconR, paL.1, pmL, hsalt, hcorr, hplain, hrecL, hrecR, hpmL, fun e hne => ?_⟩
  by_cases hcons : Consistent reconL reconR e
  · right
    obtain ⟨_, huniq⟩ := BLCSeedExtraction.unique_agreeing _ _ saltL saltR _ _ decL.2 decR.2 V.Topen V.nodes V.nodes
      reconL reconR hpureL hpureR e hne hcons
    have hmergeR : Agrees reconL reconR e (merge reconR reconL e) := by
      obtain ⟨h1, h2⟩ := BLCSeedExtraction.merge_agrees reconR reconL e (ForkSlope.consistent_symm reconL reconR e hcons)
      exact ⟨h2, h1⟩
    have hfull : fullL e = fullR e := (huniq _ hmergeR).symm
    intro a
    obtain ⟨j, hj⟩ := ForkSlope.gray_bit_ne _ _ hne
    have hL := congrFun (congrFun (congrFun hbaseL a) e) j
    have hR := congrFun (congrFun (congrFun hbaseR a) e) j
    rw [CandidateVerifier.candidateBase_affine] at hL hR
    have hslopeR : maskedSlope p saltR fullR randomCount enough auxR pmR.2 e a =
        maskedSlope p saltL fullL randomCount enough auxL pmL.2 e a := by
      simp only [maskedSlope, hsalt, hpm]
      apply Finset.sum_congr rfl
      intro c _
      rw [SlopeConsistency.slope_congr p _ _ randomCount enough _ auxL hcorr.symm,
        ForkSlope.slope_exec_congr p saltR fullR fullL randomCount enough auxL e hfull.symm]
    have hintR : Spec.BLC.consistencyColumns pmR.2 (interceptMatrix p saltR fullR randomCount enough) a e j =
        Spec.BLC.consistencyColumns pmL.2 (interceptMatrix p saltL fullL randomCount enough) a e j := by
      simp only [Spec.BLC.consistencyColumns, interceptMatrix, hsalt, hpm]
      apply Finset.sum_congr rfl
      intro c _
      rw [ForkSlope.intercept_exec_congr p saltR fullR fullL randomCount enough e hfull.symm]
    rw [hslopeR, hintR, ← hplain] at hR
    have hbases : valueL.2.2.2 a e j = valueR.2.2.2 a e j := by rw [hbase]
    rw [hL, hR] at hbases
    have hd := BLCSeedLines.zmod2_distinct_sub _ _ hj
    linear_combination hbases - (maskedSlope p saltL fullL randomCount enough auxL pmL.2 e a - auxL.plain a) * hd
  · left
    simp only [Consistent] at hcons
    push_neg at hcons
    obtain ⟨i, ls, rs, hls, hrs, hne'⟩ := hcons
    let claim : Spec.BAVCReconstructionGame.Claim lambda tau (2 ^ kappa) :=
      ⟨⟨saltL, V.expand piopL decL.1, decL.2, V.nodes⟩, ⟨saltR, V.expand piopR decR.1, decR.2, V.nodes⟩⟩
    rcases BAVCReconstructionGame.evaluated_collision V.layout V.variant V.Topen claim family
      (SharedSchemeChain.projectedResult table ciphers) reconL reconR hrecL hrecR hroot e i ls rs hls hrs hne'
      with ⟨pair, hpair⟩ | ⟨_, hseed, hcalls⟩
    · exact absurd hpair (SharedSchemeChain.projected_collision_free table ciphers hfree pair)
    · exact ⟨i, ls, rs, hseed, hcalls⟩

end
end SDitH.Proofs.ForkSlopeUniform
