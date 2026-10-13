import SDitH.Proofs.SharedSchemeChain
import SDitH.Proofs.CandidateVerifier
import SDitH.Proofs.BAVCBindingROM
import SDitH.Proofs.BAVCBinding

/-! Two successful candidate-middle verifications with equal lines digests
on one digest-collision-free table, with hidden indices differing at an
execution e, force the masked slope of e to equal the transmitted plain
check, unless a recorded seed collision occurs. The salt, corrections,
plain check and base are recovered from the chain lookups under explicit
serializer injectivity, each verification's fold is the fold of a merge-
based completion of its reconstruction, and the two completions agree at
e by uniqueness. This is the deterministic link between a successful fork
and the slope-consistency game. -/

namespace SDitH.Proofs.ForkSlope

open Spec.BAVC Spec.DomainSeparation Spec.SharedScheme Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.SlopeConsistency Spec.BLCSeedExtraction Spec.CandidateVerifier Spec.BLCSeedLines Spec.BLCSeedFold
open Spec.SlopeConsistencyGame (Out)
open scoped Classical BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

theorem projected_free (table : List Bool → Option (Out lambda s wit rnd)) (hfree : DigestCollisionFree table)
    (x y : List Bool) (d : Digest lambda) (hx : SharedSchemeChain.projected table x = some d)
    (hy : SharedSchemeChain.projected table y = some d) : x = y := by
  obtain ⟨px, hpx, hdx⟩ := Option.map_eq_some_iff.mp hx
  obtain ⟨py, hpy, hdy⟩ := Option.map_eq_some_iff.mp hy
  exact hfree x y px py hpx hpy (hdx.trans hdy.symm)

/-- Equal roots of two successful reconstructions on one collision-free
projected table give equal salts, through the recorded outer lookups. -/
theorem salt_eq_of_hcom_eq (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (Topen : Nat) (nodes : NodesBinding lambda tau (2 ^ kappa))
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (hfree : DigestCollisionFree table)
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (saltL saltR : Bits lambda) (hiddenL hiddenR : Fin tau → Fin (2 ^ kappa)) (openingL openingR : Opening lambda tau)
    (reconL reconR : Reconstructed lambda tau (2 ^ kappa))
    (hl : Evaluates family (SharedSchemeChain.projected table) ciphers
      (Spec.BAVCReconstructionProgram.reconstruct layout variant saltL hiddenL openingL Topen nodes) (Except.ok reconL))
    (hr : Evaluates family (SharedSchemeChain.projected table) ciphers
      (Spec.BAVCReconstructionProgram.reconstruct layout variant saltR hiddenR openingR Topen nodes) (Except.ok reconR))
    (hroot : reconL.hcom = reconR.hcom) : saltL = saltR := by
  let p := Spec.BAVCReconstructionProgram.primitives (tau := tau) (N := 2 ^ kappa) layout variant family
    (SharedSchemeChain.projected table)
  obtain ⟨rowsL, _, hvalL, hobsL⟩ := (BAVCReconstructionProgram.reconstruction_evaluates layout variant family _ ciphers
    saltL hiddenL openingL Topen nodes _ hl).2 reconL rfl
  obtain ⟨rowsR, _, hvalR, hobsR⟩ := (BAVCReconstructionProgram.reconstruction_evaluates layout variant family _ ciphers
    saltR hiddenR openingR Topen nodes _ hr).2 reconR rfl
  have htable : Spec.BAVCBindingROM.withTable p (SharedSchemeChain.projected table) = p := rfl
  have hlookL := BAVCBindingROM.observed_lookup p _ saltL _ hobsL _ (BAVCBinding.outerQuery_mem _ _ _)
  have hlookR := BAVCBindingROM.observed_lookup p _ saltR _ hobsR _ (BAVCBinding.outerQuery_mem _ _ _)
  rw [htable] at hlookL hlookR
  have hhcomL : reconL.hcom = p.hash (Spec.BAVCBinding.outerQuery p saltL (Spec.BAVCBinding.rowCommitments rowsL)) := by
    rw [hvalL]
    rfl
  have hhcomR : reconR.hcom = p.hash (Spec.BAVCBinding.outerQuery p saltR (Spec.BAVCBinding.rowCommitments rowsR)) := by
    rw [hvalR]
    rfl
  have heq := projected_free table hfree _ _ _ hlookL (by rw [hlookR, ← hhcomR, ← hroot, hhcomL])
  exact (BAVCBinding.outerQuery_eq p saltL saltR _ _ heq).1

theorem randomTable_congr (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full full' : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau) (h : full e = full' e) :
    Spec.BLCCommit.randomTable p salt full randomCount enough e =
      Spec.BLCCommit.randomTable p salt full' randomCount enough e := by
  funext i j
  simp only [Spec.BLCCommit.randomTable, h]

theorem slope_exec_congr (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full full' : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : Spec.BLCCommit.Auxiliary tau s wit rnd)
    (e : Fin tau) (h : full e = full' e) (c : Fin (s + (wit + rnd))) :
    Spec.BLCSeedFold.slope p salt full randomCount enough aux e c =
      Spec.BLCSeedFold.slope p salt full' randomCount enough aux e c := by
  simp only [Spec.BLCSeedFold.slope, folded, randomTable_congr p salt full full' randomCount enough e h]

theorem intercept_exec_congr (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full full' : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (e : Fin tau) (h : full e = full' e)
    (c : Fin (s + (wit + rnd))) (j : Fin kappa) :
    intercept p salt full randomCount enough e c j = intercept p salt full' randomCount enough e c j := by
  simp only [intercept, folded, randomTable_congr p salt full full' randomCount enough e h]

theorem merge_left_revealed (left right : Reconstructed lambda tau (2 ^ kappa)) (e : Fin tau) (i : Fin (2 ^ kappa))
    (seed : Seed lambda) (h : left.seeds e i = some seed) : merge left right e i = seed := by
  simp [merge, h]

theorem consistent_symm (left right : Reconstructed lambda tau (2 ^ kappa)) (e : Fin tau)
    (h : Consistent left right e) : Consistent right left e :=
  fun i ls rs hls hrs => (h i rs ls hrs hls).symm

theorem gray_bit_ne (a b : Fin (2 ^ kappa)) (h : a ≠ b) :
    ∃ j, Spec.GrayCode.grayFieldRow a j ≠ Spec.GrayCode.grayFieldRow b j := by
  by_contra hall
  push_neg at hall
  exact h (GrayCode.grayFieldRow_injective (funext hall))

/-- Two candidate-middle verifications of a fork: at an execution where the
hidden indices differ, the masked slope equals the plain check, unless a
recorded seed collision occurs. -/
theorem fork_masked_slope {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
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
    (hlines : left.lines = right.lines) (hfree : DigestCollisionFree table)
    (e : Fin tau) (hne : V.expand piopL decL.1 e ≠ V.expand piopR decR.1 e) :
    (∃ (i : Fin (2 ^ kappa)) (ls rs : Seed lambda), saltL = saltR ∧
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
      ∃ (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (M : Spec.SlopeConsistencyGame.Mask s wit rnd),
        saltL = saltR ∧ auxL.corrections = auxR.corrections ∧ auxL.plain = auxR.plain ∧
        ∀ a, maskedSlope p saltL full randomCount enough auxL M e a = auxL.plain a := by
  obtain ⟨reconL, paL, plL, valueL, hrecL, hpaL, hmidL, hplL, hleft⟩ :=
    SharedSchemeChain.verify_evaluates V saltL auxL piopL decL family table ciphers left hl
  obtain ⟨reconR, paR, plR, valueR, hrecR, hpaR, hmidR, hplR, hright⟩ :=
    SharedSchemeChain.verify_evaluates V saltR auxR piopR decR family table ciphers right hr
  -- Lines digests: same query strings, hence same auxiliary digest, plain and base.
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
  -- Auxiliary strings: same root and corrections.
  have haq := hfree _ _ paL paR hpaL hpaR hpa1
  have hroot : reconL.hcom = reconR.hcom := Proofs.BLCHashChain.aux_header reconL.hcom reconR.hcom _ _ haq
  have hcorr : auxL.corrections = auxR.corrections := by
    have he := List.append_cancel_left haq
    exact hencoding (List.append_inj he (by simp)).2
  have hsalt : saltL = saltR := salt_eq_of_hcom_eq V.layout V.variant V.Topen V.nodes family table hfree ciphers
    saltL saltR _ _ decL.2 decR.2 reconL reconR hrecL hrecR hroot
  by_cases hcons : Consistent reconL reconR e
  · right
    -- Completions of the two reconstructions, agreeing at e.
    let fullL : Fin tau → Fin (2 ^ kappa) → Bits lambda := fun e' i => merge reconL reconR e' i
    let fullR : Fin tau → Fin (2 ^ kappa) → Bits lambda := fun e' i => merge reconR reconL e' i
    have hagreeL : ∀ e' i, i ≠ V.expand piopL decL.1 e' → reconL.seeds e' i = some (fullL e' i) := by
      intro e' i hi
      obtain ⟨seed, hseed⟩ := BLCSeedExtraction.reconstructed_revealed_present _ saltL _ decL.2 V.Topen V.nodes reconL
        (BAVCReconstructionProgram.reconstruction_evaluates V.layout V.variant family _ ciphers saltL _ decL.2 V.Topen V.nodes _ hrecL).1
        e' i hi
      rw [hseed]
      simp only [fullL, merge_left_revealed reconL reconR e' i seed hseed]
    have hagreeR : ∀ e' i, i ≠ V.expand piopR decR.1 e' → reconR.seeds e' i = some (fullR e' i) := by
      intro e' i hi
      obtain ⟨seed, hseed⟩ := BLCSeedExtraction.reconstructed_revealed_present _ saltR _ decR.2 V.Topen V.nodes reconR
        (BAVCReconstructionProgram.reconstruction_evaluates V.layout V.variant family _ ciphers saltR _ decR.2 V.Topen V.nodes _ hrecR).1
        e' i hi
      rw [hseed]
      simp only [fullR, merge_left_revealed reconR reconL e' i seed hseed]
    rw [hmid] at hmidL hmidR
    obtain ⟨pmL, hpmL, _, _, _, hbaseL⟩ := CandidateVerifier.candidateMiddle_evaluates xi p V.nodes encode randomCount enough
      saltL auxL _ reconL paL.1 fullL hagreeL family table ciphers valueL hmidL
    obtain ⟨pmR, hpmR, _, _, _, hbaseR⟩ := CandidateVerifier.candidateMiddle_evaluates xi p V.nodes encode randomCount enough
      saltR auxR _ reconR paR.1 fullR hagreeR family table ciphers valueR hmidR
    have hpm : pmL = pmR := by
      rw [hpa1] at hpmL
      exact Option.some.inj (hpmL.symm.trans hpmR)
    -- The completions agree at e.
    have hpureL := (BAVCReconstructionProgram.reconstruction_evaluates V.layout V.variant family _ ciphers
      saltL _ decL.2 V.Topen V.nodes _ hrecL).1
    have hpureR := (BAVCReconstructionProgram.reconstruction_evaluates V.layout V.variant family _ ciphers
      saltR _ decR.2 V.Topen V.nodes _ hrecR).1
    obtain ⟨_, huniq⟩ := BLCSeedExtraction.unique_agreeing _ _ saltL saltR _ _ decL.2 decR.2 V.Topen V.nodes V.nodes
      reconL reconR hpureL hpureR e hne hcons
    have hmergeR : Agrees reconL reconR e (merge reconR reconL e) := by
      obtain ⟨h1, h2⟩ := BLCSeedExtraction.merge_agrees reconR reconL e (consistent_symm reconL reconR e hcons)
      exact ⟨h2, h1⟩
    have hfull : fullL e = fullR e := (huniq _ hmergeR).symm
    refine ⟨fullL, pmL.2, hsalt, hcorr, hplain, fun a => ?_⟩
    obtain ⟨j, hj⟩ := gray_bit_ne _ _ hne
    -- Both bases at (a, e, j), in the fullL/saltL/auxL quantities.
    have hL := congrFun (congrFun (congrFun hbaseL a) e) j
    have hR := congrFun (congrFun (congrFun hbaseR a) e) j
    rw [CandidateVerifier.candidateBase_affine] at hL hR
    have hslopeR : maskedSlope p saltR fullR randomCount enough auxR pmR.2 e a =
        maskedSlope p saltL fullL randomCount enough auxL pmL.2 e a := by
      simp only [maskedSlope, hsalt, hpm]
      apply Finset.sum_congr rfl
      intro c _
      rw [SlopeConsistency.slope_congr p _ _ randomCount enough _ auxL hcorr.symm,
        slope_exec_congr p saltR fullR fullL randomCount enough auxL e hfull.symm]
    have hintR : Spec.BLC.consistencyColumns pmR.2 (interceptMatrix p saltR fullR randomCount enough) a e j =
        Spec.BLC.consistencyColumns pmL.2 (interceptMatrix p saltL fullL randomCount enough) a e j := by
      simp only [Spec.BLC.consistencyColumns, interceptMatrix, hsalt, hpm]
      apply Finset.sum_congr rfl
      intro c _
      rw [intercept_exec_congr p saltR fullR fullL randomCount enough e hfull.symm]
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
      with ⟨pair, hpair⟩ | ⟨hsalt', hseed, hcalls⟩
    · exact absurd hpair (SharedSchemeChain.projected_collision_free table ciphers hfree pair)
    · exact ⟨i, ls, rs, hsalt', hseed, hcalls⟩

end
end SDitH.Proofs.ForkSlope
