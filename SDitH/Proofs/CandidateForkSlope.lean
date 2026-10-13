import SDitH.Proofs.CandidateSchemeChain
import SDitH.Proofs.ForkSlope
import SDitH.Proofs.CandidateVerifier

/-! The fork-to-slope lemma for the candidate scheme. Two candidate-middle
verifications over the candidate reconstruction on one collision-free
table with equal lines digests share the auxiliary digest, mask, plain
check, base, corrections, root, salt and recomputed commitments. Each
opening is completed by the other's revealed seed at its own hidden
index; at every execution where the hidden indices differ, either two
revealed seeds with the same commitment differ (a recorded seed
collision), or the two completions agree there and the masked slope at
the stored mask equals the plain check. -/

namespace SDitH.Proofs.CandidateForkSlope

open Spec.BAVC Spec.DomainSeparation Spec.SharedScheme Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.SlopeConsistency Spec.CandidateVerifier Spec.BLCSeedLines Spec.BLCSeedFold Spec.CandidateBAVC Spec.CandidateScheme
open Spec.SlopeConsistencyGame (Out)
open CandidateBAVC (leafValue induced)
open SharedSigner (expandEntries)
open scoped Classical BigOperators
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- An opening completed by another at its own hidden index. -/
def completion (hidden : Fin tau → Fin (2 ^ kappa)) (self other : Opening lambda tau (2 ^ kappa))
    (e : Fin tau) (i : Fin (2 ^ kappa)) : Seed lambda :=
  if i = hidden e then (other.revealed e i).getD (fun _ => false) else (self.revealed e i).getD (fun _ => false)

theorem completion_self (hidden : Fin tau → Fin (2 ^ kappa)) (self other : Opening lambda tau (2 ^ kappa))
    (e : Fin tau) (i : Fin (2 ^ kappa)) (hi : i ≠ hidden e) (seed : Seed lambda) (h : self.revealed e i = some seed) :
    completion hidden self other e i = seed := by
  simp [completion, hi, h]

theorem completion_other (hidden : Fin tau → Fin (2 ^ kappa)) (self other : Opening lambda tau (2 ^ kappa))
    (e : Fin tau) (i : Fin (2 ^ kappa)) (hi : i = hidden e) :
    completion hidden self other e i = (other.revealed e i).getD (fun _ => false) := by
  simp [completion, hi]

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
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau (2 ^ kappa))
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (left right : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family table ciphers (Spec.CandidateScheme.verifyProgram V saltL auxL piopL decL) (Except.ok left))
    (hr : Evaluates family table ciphers (Spec.CandidateScheme.verifyProgram V saltR auxR piopR decR) (Except.ok right))
    (hlines : left.lines = right.lines) (hfree : DigestCollisionFree table) :
    ∃ (reconL reconR : Reconstructed lambda tau (2 ^ kappa)) (auxD : Digest lambda) (pm : Out lambda s wit rnd),
      saltL = saltR ∧ auxL.corrections = auxR.corrections ∧ auxL.plain = auxR.plain ∧
      Evaluates family table ciphers
        (Spec.CandidateBAVC.reconstruct V.layout V.variant saltL (V.expand piopL decL.1) decL.2) (Except.ok reconL) ∧
      Evaluates family table ciphers
        (Spec.CandidateBAVC.reconstruct V.layout V.variant saltR (V.expand piopR decR.1) decR.2) (Except.ok reconR) ∧
      table (Spec.BAVCChainInputs.maskInput auxD) = some pm ∧
      (∃ pa, table (Spec.BLCHashChain.auxQuery reconL.hcom (Spec.BLCHashChain.sourceTail V.encoding auxL.corrections)) =
        some pa ∧ pa.1 = auxD) ∧
      commitsOf (leafValue family V.layout V.variant saltL (V.expand piopL decL.1) decL.2) =
        commitsOf (leafValue family V.layout V.variant saltR (V.expand piopR decR.1) decR.2) ∧
      ∀ e : Fin tau, V.expand piopL decL.1 e ≠ V.expand piopR decR.1 e →
        (∃ (i : Fin (2 ^ kappa)) (ls rs : Seed lambda),
            Spec.BAVCBinding.IsSeedCollision (induced (tau := tau) (kappa := kappa) family table V.layout V.variant) saltL
              (Spec.SeedTree.leafOffset e i) ls rs ∧
            expandEntries family ciphers V.layout V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) ls ∧
            expandEntries family ciphers V.layout V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) rs) ∨
          (completion (V.expand piopL decL.1) decL.2 decR.2 e = completion (V.expand piopR decR.1) decR.2 decL.2 e ∧
            ∀ a, maskedSlope p saltL (completion (V.expand piopL decL.1) decL.2 decR.2) randomCount enough auxL pm.2 e a =
              auxL.plain a) := by
  obtain ⟨reconL, paL, plL, valueL, hrecL, hpaL, hmidL, hplL, hleft⟩ :=
    CandidateSchemeChain.verify_evaluates family table ciphers V saltL auxL piopL decL left hl
  obtain ⟨reconR, paR, plR, valueR, hrecR, hpaR, hmidR, hplR, hright⟩ :=
    CandidateSchemeChain.verify_evaluates family table ciphers V saltR auxR piopR decR right hr
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
  -- Reconstruction facts.
  obtain ⟨hseedsL, hhcomL, hrowsL, houterL, hhidL, hrevL⟩ :=
    CandidateBAVC.reconstruct_evaluates family table ciphers V.layout V.variant saltL _ decL.2 reconL hrecL
  obtain ⟨hseedsR, hhcomR, hrowsR, houterR, hhidR, hrevR⟩ :=
    CandidateBAVC.reconstruct_evaluates family table ciphers V.layout V.variant saltR _ decR.2 reconR hrecR
  set P := induced (tau := tau) (kappa := kappa) family table V.layout V.variant with hP
  set CL := commitsOf (leafValue family V.layout V.variant saltL (V.expand piopL decL.1) decL.2) with hCL
  set CR := commitsOf (leafValue family V.layout V.variant saltR (V.expand piopR decR.1) decR.2) with hCR
  -- Salt and commitments.
  obtain ⟨pairOL, hOL, hOL1⟩ := houterL
  obtain ⟨pairOR, hOR, hOR1⟩ := houterR
  have hOeq : Spec.BAVCBinding.outerQuery P saltL CL = Spec.BAVCBinding.outerQuery P saltR CR :=
    hfree _ _ pairOL pairOR hOL hOR (by rw [hOL1, hOR1, hroot])
  obtain ⟨hsalt, hrowhash⟩ := BAVCBinding.outerQuery_eq P saltL saltR CL CR hOeq
  subst hsalt
  have hC : CL = CR := by
    funext e
    obtain ⟨pL, hpL, hpL1⟩ := hrowsL e
    obtain ⟨pR, hpR, hpR1⟩ := hrowsR e
    have hq : Spec.BAVCBinding.rowQuery CL e = Spec.BAVCBinding.rowQuery CR e :=
      hfree _ _ pL pR hpL hpR (by rw [hpL1, hpR1]; exact congrFun hrowhash e)
    exact BAVCBinding.rowQuery_injective CL CR e hq
  -- Completions and the candidate middle's evaluations.
  let fullL := completion (V.expand piopL decL.1) decL.2 decR.2
  let fullR := completion (V.expand piopR decR.1) decR.2 decL.2
  have hagreeL : ∀ e i, i ≠ V.expand piopL decL.1 e → reconL.seeds e i = some (fullL e i) := by
    intro e i hi
    obtain ⟨seed, hseed, _, _⟩ := hrevL e i hi
    show reconL.seeds e i = some (completion (V.expand piopL decL.1) decL.2 decR.2 e i)
    rw [hseedsL, hseed, completion_self _ _ _ e i hi seed hseed]
  have hagreeR : ∀ e i, i ≠ V.expand piopR decR.1 e → reconR.seeds e i = some (fullR e i) := by
    intro e i hi
    obtain ⟨seed, hseed, _, _⟩ := hrevR e i hi
    show reconR.seeds e i = some (completion (V.expand piopR decR.1) decR.2 decL.2 e i)
    rw [hseedsR, hseed, completion_self _ _ _ e i hi seed hseed]
  rw [hmid] at hmidL hmidR
  obtain ⟨pmL, hpmL, _, _, _, hbaseL⟩ := CandidateVerifier.candidateMiddle_evaluates xi p V.nodes encode randomCount enough
    saltL auxL _ reconL paL.1 fullL hagreeL family table ciphers valueL hmidL
  obtain ⟨pmR, hpmR, _, _, _, hbaseR⟩ := CandidateVerifier.candidateMiddle_evaluates xi p V.nodes encode randomCount enough
    saltL auxR _ reconR paR.1 fullR hagreeR family table ciphers valueR hmidR
  have hpm : pmL = pmR := by
    rw [hpa1] at hpmL
    exact Option.some.inj (hpmL.symm.trans hpmR)
  refine ⟨reconL, reconR, paL.1, pmL, rfl, hcorr, hplain, hrecL, hrecR, hpmL, ⟨paL, hpaL, rfl⟩, hC, fun e hne => ?_⟩
  by_cases hcol : ∃ (i : Fin (2 ^ kappa)) (ls rs : Seed lambda),
      Spec.BAVCBinding.IsSeedCollision P saltL (Spec.SeedTree.leafOffset e i) ls rs ∧
      expandEntries family ciphers V.layout V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) ls ∧
      expandEntries family ciphers V.layout V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) rs
  · exact Or.inl hcol
  right
  -- The completions agree at e.
  have hfull : fullL e = fullR e := by
    funext i
    by_cases hiL : i = V.expand piopL decL.1 e
    · have hiR : i ≠ V.expand piopR decR.1 e := by rw [hiL]; exact hne
      show completion _ _ _ e i = completion _ _ _ e i
      rw [completion_other _ _ _ e i hiL]
      obtain ⟨seed, hseed, _, _⟩ := hrevR e i hiR
      rw [completion_self _ _ _ e i hiR seed hseed, hseed]
      rfl
    · by_cases hiR : i = V.expand piopR decR.1 e
      · show completion _ _ _ e i = completion _ _ _ e i
        rw [completion_other _ _ _ e i hiR]
        obtain ⟨seed, hseed, _, _⟩ := hrevL e i hiL
        rw [completion_self _ _ _ e i hiL seed hseed, hseed]
        rfl
      · obtain ⟨sL, hsL, hCLi, hentL⟩ := hrevL e i hiL
        obtain ⟨sR, hsR, hCRi, hentR⟩ := hrevR e i hiR
        show completion _ _ _ e i = completion _ _ _ e i
        rw [completion_self _ _ _ e i hiL sL hsL, completion_self _ _ _ e i hiR sR hsR]
        by_contra hne'
        apply hcol
        refine ⟨i, sL, sR, ⟨hne', ?_⟩, hentL, hentR⟩
        have := congrFun (congrFun hC e) i
        rw [hCLi, hCRi] at this
        exact this
  refine ⟨hfull, fun a => ?_⟩
  obtain ⟨j, hj⟩ := ForkSlope.gray_bit_ne _ _ hne
  have hL := congrFun (congrFun (congrFun hbaseL a) e) j
  have hR := congrFun (congrFun (congrFun hbaseR a) e) j
  rw [CandidateVerifier.candidateBase_affine] at hL hR
  have hslopeR : maskedSlope p saltL fullR randomCount enough auxR pmR.2 e a =
      maskedSlope p saltL fullL randomCount enough auxL pmL.2 e a := by
    simp only [maskedSlope, hpm]
    apply Finset.sum_congr rfl
    intro c _
    rw [SlopeConsistency.slope_congr p _ _ randomCount enough _ auxL hcorr.symm,
      ForkSlope.slope_exec_congr p saltL fullR fullL randomCount enough auxL e hfull.symm]
  have hintR : Spec.BLC.consistencyColumns pmR.2 (interceptMatrix p saltL fullR randomCount enough) a e j =
      Spec.BLC.consistencyColumns pmL.2 (interceptMatrix p saltL fullL randomCount enough) a e j := by
    simp only [Spec.BLC.consistencyColumns, interceptMatrix, hpm]
    apply Finset.sum_congr rfl
    intro c _
    rw [ForkSlope.intercept_exec_congr p saltL fullR fullL randomCount enough e hfull.symm]
  rw [hslopeR, hintR, ← hplain] at hR
  have hbases : valueL.2.2.2 a e j = valueR.2.2.2 a e j := by rw [hbase]
  rw [hL, hR] at hbases
  have hd := BLCSeedLines.zmod2_distinct_sub _ _ hj
  linear_combination hbases - (maskedSlope p saltL fullL randomCount enough auxL pmL.2 e a - auxL.plain a) * hd

end
end SDitH.Proofs.CandidateForkSlope
