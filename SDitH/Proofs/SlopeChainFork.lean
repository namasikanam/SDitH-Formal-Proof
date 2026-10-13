import SDitH.Proofs.SlopeEventSetting

/-! A winning fork without the charged events is one of the named events or
an extraction, with the stored-mask slope event in place of the
existential-mask one: under the identity layout, the first branch's
claim (its salt, the completed seed vector, the recomputed row hashes and
root, the auxiliary digest and the auxiliary data) is chained in the
snapshot's table, every seed's expansion is recorded in the union of the
two histories (the revealed seeds by the first branch's reconstruction,
the hidden ones by the second's), and the slopes differ but agree under
the stored mask. -/

namespace SDitH.Proofs.SlopeChainFork

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.HashCipherEvaluation Spec.CandidateVerifier
open Spec.SlopeConsistency Spec.BLCSeedLines Spec.BLCSeedFold Spec.ConsistencyMatrix Spec.CandidateBAVC
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher Spec.SeedPrimitives Spec.SharedSlopeGame Spec.BAVCChainInputs Spec.SeedPairing
open BranchAccounting (MaskAfterCut)
open CandidateBAVC (leafValue induced)
open SharedSigner (expandEntries)
open CandidateForkSlope (completion completion_self completion_other)
open CandidateReduction SlopeEventSetting
open scoped Classical

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- A winning fork without the charged events is one of the named events,
with the stored-mask slope event, or an extraction. -/
theorem good_implies_events_C (hlayout : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support)
    (hgood : (forkWins snapshot.input result && !CandidateForkOutcome.forkBad (tau := tau) snapshot result) = true) :
    (maskAfter snapshot result || notSeparated V result || seedCollision V snapshot result ||
      slopeWinC S V snapshot result || zeroChallenge V encode result || schwartzZippel S V encode snapshot result ||
      extracts S V snapshot result) = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hgood
  obtain ⟨left, right, a, b, bodyA, bodyB, hres, ha, hb, hbodyA, hbodyB, _, hext⟩ :=
    ForkExtraction.fork_extracts S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
      hlinesEnc hencode index fuel c hc snapshot hsnap result hr hgood.1 hgood.2
  subst hres
  simp only [maskAfter, notSeparated, seedCollision, slopeWinC, zeroChallenge, schwartzZippel, extracts, onAttempts, ha, hb,
    hbodyA, hbodyB, Bool.or_eq_true, decide_eq_true_eq]
  by_cases hmask : MaskAfterCut snapshot.world.other.hashTable a.world.other.hashTable ∨
      MaskAfterCut snapshot.world.other.hashTable b.world.other.hashTable
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hmask)))))
  by_cases hsep : ∃ e, V.expand a.signature.piop bodyA.2.2.1.1 e = V.expand b.signature.piop bodyB.2.2.1.1 e
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hsep)))))
  obtain ⟨reconA, reconB, pa, pm, hsaltAB, hrecA, hrecB, hC, hpa, hpm, hM⟩ :=
    hext (fun h => hmask (Or.inl h)) (fun h => hmask (Or.inr h)) (fun e h => hsep ⟨e, h⟩)
  rcases hM with hcol | hwin | ⟨u, hu, hvan⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hcol))))
  · -- the stored-mask slope event
    refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
    set fam := snapshot.world.other.family with hfam
    set P := snapshot.world.other.hashTable with hP
    set U := a.world.other.cipherHistory ++ b.world.other.cipherHistory with hU
    set hidA := V.expand a.signature.piop bodyA.2.2.1.1 with hhidA
    set hidB := V.expand b.signature.piop bodyB.2.2.1.1 with hhidB
    rw [hlayout] at hrecA hrecB hC
    obtain ⟨hseedsA, hhcomA, hrowsA, houterA, hhidcA, hrevA⟩ :=
      CandidateBAVC.reconstruct_evaluates fam P U _ V.variant bodyA.1 hidA bodyA.2.2.1.2 reconA hrecA
    obtain ⟨hseedsB, -, -, -, -, hrevB⟩ :=
      CandidateBAVC.reconstruct_evaluates fam P U _ V.variant bodyB.1 hidB bodyB.2.2.1.2 reconB hrecB
    set CA := commitsOf (leafValue fam (Spec.BAVCCipherProgram.fullLayout lambda) V.variant bodyA.1 hidA bodyA.2.2.1.2) with hCA
    set CB := commitsOf (leafValue fam (Spec.BAVCCipherProgram.fullLayout lambda) V.variant bodyB.1 hidB bodyB.2.2.1.2) with hCB
    set prim := induced (tau := tau) (kappa := kappa) fam P (Spec.BAVCCipherProgram.fullLayout lambda) V.variant with hprim
    have hsep' : ∀ e, hidA e ≠ hidB e := fun e h => hsep ⟨e, h⟩
    -- the completed seed vector's commitments are the first branch's
    have hfullc : ∀ e i, commitOf (tau := tau) (kappa := kappa) V.variant fam bodyA.1 e i (fullOf V a bodyA bodyB e i) = CA e i := by
      intro e i
      by_cases hi : i = hidA e
      · have hiB : i ≠ hidB e := by rw [hi]; exact hsep' e
        obtain ⟨seed, hseed, hCBi, -⟩ := hrevB e i hiB
        have hfull : fullOf V a bodyA bodyB e i = seed := by
          show completion hidA bodyA.2.2.1.2 bodyB.2.2.1.2 e i = seed
          rw [completion_other _ _ _ e i hi, hseed]
          rfl
        rw [hfull, hC, hCBi, hsaltAB]
        rfl
      · obtain ⟨seed, hseed, hCAi, -⟩ := hrevA e i hi
        have hfull : fullOf V a bodyA bodyB e i = seed := completion_self _ _ _ e i hi seed hseed
        rw [hfull, hCAi]
        rfl
    let cl : Claim lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) :=
      ⟨bodyA.1, fullOf V a bodyA bodyB, fun e => prim.hash (Spec.BAVCBinding.rowQuery CA e), reconA.hcom, pa.1, bodyA.2.1⟩
    have hrows : ∀ e, rows (commitOf (tau := tau) (kappa := kappa) V.variant fam bodyA.1) cl e = CA e :=
      fun e => funext fun i => hfullc e i
    refine ⟨cl, rfl, rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, pm, hpm, ?_⟩
    · intro e
      obtain ⟨pair, hp, hp1⟩ := hrowsA e
      refine ⟨pair, ?_, hp1⟩
      show P (rowString (rows (commitOf (tau := tau) (kappa := kappa) V.variant fam bodyA.1) cl e)) = some pair
      rw [hrows e]
      exact hp
    · obtain ⟨pair, hp, hp1⟩ := houterA
      exact ⟨pair, hp, hp1⟩
    · exact ⟨pa, hpa, rfl⟩
    · intro e i
      by_cases hi : i = hidA e
      · have hiB : i ≠ hidB e := by rw [hi]; exact hsep' e
        obtain ⟨seed, hseed, -, hent⟩ := hrevB e i hiB
        have hfull : fullOf V a bodyA bodyB e i = seed := by
          show completion hidA bodyA.2.2.1.2 bodyB.2.2.1.2 e i = seed
          rw [completion_other _ _ _ e i hi, hseed]
          rfl
        rw [← hsaltAB] at hent
        have hq := expandEntries_fullLayout hl hL fam U V.variant bodyA.1 seed e i hent
        show seedEntry fam (fullOf V a bodyA bodyB e i) (input0 V.variant bodyA.1 e i) ∈ U ∧
          seedEntry fam (fullOf V a bodyA bodyB e i) (companion (input0 V.variant bodyA.1 e i)) ∈ U
        rw [hfull]
        exact hq
      · obtain ⟨seed, hseed, -, hent⟩ := hrevA e i hi
        have hfull : fullOf V a bodyA bodyB e i = seed := completion_self _ _ _ e i hi seed hseed
        have hq := expandEntries_fullLayout hl hL fam U V.variant bodyA.1 seed e i hent
        show seedEntry fam (fullOf V a bodyA bodyB e i) (input0 V.variant bodyA.1 e i) ∈ U ∧
          seedEntry fam (fullOf V a bodyA bodyB e i) (companion (input0 V.variant bodyA.1 e i)) ∈ U
        rw [hfull]
        exact hq
    · obtain ⟨e, e', hne, hmask⟩ := hwin
      exact ⟨e, e', hne, hmask⟩
  by_cases hz : encode (V.expand a.signature.piop bodyA.2.2.1.1) = 0
  · exact Or.inl (Or.inl (Or.inr hz))
  by_cases hdiff : difference S V snapshot a bodyA bodyB u = 0
  · exact Or.inr ⟨u, hu, hdiff⟩
  · exact Or.inl (Or.inr ⟨u, hu, hdiff, hvan hz⟩)

end
end SDitH.Proofs.SlopeChainFork
