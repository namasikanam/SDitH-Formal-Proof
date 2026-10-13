import SDitH.Proofs.CandidateForkOutcome
import SDitH.Proofs.CandidateCompleteness
import SDitH.Proofs.PIOPExtraction
import SDitH.Proofs.SlopeConsistencyLink

/-! The deterministic extraction from a good candidate fork. Under the
user's decisions, a successful fork without the charged events whose two
branches read their masks before the fork and whose hidden indices differ
at every execution yields, from the two accepted transcripts, either a
recorded seed collision, or the slope-consistency game's winning
condition at the stored mask, or a common slope for the first branch's
transcript together with the vanishing of the extracted lines' prover
polynomial minus the hashed coefficient polynomial at that branch's
inverted challenge. Each named alternative is a probabilistic event to be
charged; the extracted witness is the corrections plus the common slope. -/

namespace SDitH.Proofs.ForkExtraction

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.HashCipherEvaluation Spec.CandidateVerifier
open Spec.SlopeConsistency Spec.BLCSeedLines Spec.BLCSeedFold Spec.ConsistencyMatrix Spec.CandidateBAVC
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open BranchAccounting (MaskAfterCut)
open CandidateBranch (UniformSlope)
open CandidateBAVC (leafValue)
open Spec.BAVC (Reconstructed)
open CandidateForkSlope (completion)
open CandidateBAVC (induced)
open SharedSigner (expandEntries)
open PIOPExtraction (witnessLine randomnessLine)
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

/-- The extraction from a good candidate fork. -/
theorem fork_extracts (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
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
    (hw : forkWins snapshot.input result = true)
    (hgood : CandidateForkOutcome.forkBad (tau := tau) snapshot result = false) :
    ∃ left right a b bodyA bodyB, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧ a.target ≠ b.target ∧
      (¬ MaskAfterCut snapshot.world.other.hashTable a.world.other.hashTable →
       ¬ MaskAfterCut snapshot.world.other.hashTable b.world.other.hashTable →
       (∀ e, V.expand a.signature.piop bodyA.2.2.1.1 e ≠ V.expand b.signature.piop bodyB.2.2.1.1 e) →
       ∃ (reconA reconB : Reconstructed lambda tau (2 ^ kappa))
         (pa pm : Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))),
         bodyA.1 = bodyB.1 ∧
         Evaluates snapshot.world.other.family snapshot.world.other.hashTable
           (a.world.other.cipherHistory ++ b.world.other.cipherHistory)
           (Spec.CandidateBAVC.reconstruct V.layout V.variant bodyA.1 (V.expand a.signature.piop bodyA.2.2.1.1) bodyA.2.2.1.2)
           (Except.ok reconA) ∧
         Evaluates snapshot.world.other.family snapshot.world.other.hashTable
           (a.world.other.cipherHistory ++ b.world.other.cipherHistory)
           (Spec.CandidateBAVC.reconstruct V.layout V.variant bodyB.1 (V.expand b.signature.piop bodyB.2.2.1.1) bodyB.2.2.1.2)
           (Except.ok reconB) ∧
         commitsOf (leafValue snapshot.world.other.family V.layout V.variant bodyA.1 (V.expand a.signature.piop bodyA.2.2.1.1)
             bodyA.2.2.1.2) =
           commitsOf (leafValue snapshot.world.other.family V.layout V.variant bodyB.1 (V.expand b.signature.piop bodyB.2.2.1.1)
             bodyB.2.2.1.2) ∧
         snapshot.world.other.hashTable (Spec.BLCHashChain.auxQuery reconA.hcom
           (Spec.BLCHashChain.sourceTail V.encoding bodyA.2.1.corrections)) = some pa ∧
         snapshot.world.other.hashTable (Spec.BAVCChainInputs.maskInput pa.1) = some pm ∧
         let full := completion (V.expand a.signature.piop bodyA.2.2.1.1) bodyA.2.2.1.2 bodyB.2.2.1.2
         let slopes := fun e => Spec.BLCSeedFold.slope S.signer.p bodyA.1 full S.signer.randomCount S.signer.enough bodyA.2.1 e
         (∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (ls rs : Spec.BAVC.Seed lambda),
            Spec.BAVCBinding.IsSeedCollision
              (induced (tau := tau) (kappa := kappa) snapshot.world.other.family snapshot.world.other.hashTable V.layout V.variant)
              bodyA.1 (Spec.SeedTree.leafOffset e i) ls rs ∧
            expandEntries snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) V.layout
              V.variant bodyA.1 (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) ls ∧
            expandEntries snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) V.layout
              V.variant bodyA.1 (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) rs) ∨
         (∃ e e', slopes e ≠ slopes e' ∧ ∀ a', masked pm.2 (slopes e) a' = masked pm.2 (slopes e') a') ∨
         ∃ u : Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2,
           (∀ e c', slopes e c' = u c') ∧
           (encode (V.expand a.signature.piop bodyA.2.2.1.1) ≠ 0 →
             (Spec.PIOPComposition.proverRun widths S.hsize S.signer.xi (S.expandBatching snapshot.input.payload.1).1
                (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
                (witnessLine S.signer.xi S.signer.p bodyA.1 full S.signer.randomCount S.signer.enough bodyA.2.1 u)
                (randomnessLine S.signer.xi S.signer.p bodyA.1 full S.signer.randomCount S.signer.enough u) -
              Spec.CoefficientCompression.coefficientPolynomial snapshot.input.payload.2).eval
                (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ = 0)) := by
  obtain ⟨left, right, a, b, bodyA, bodyB, recA, recB, hres, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB, hlinesA,
    hlinesB, hcoeffs, houtcome⟩ := CandidateForkOutcome.fork_good_outcome S V verifyBudget publicKey sampleWitness adversary
    hlambda htau S.signer.xi S.signer.p encode S.signer.randomCount S.signer.enough hmid hencoding hlinesEnc index fuel c hc
    snapshot hsnap result hr hw hgood
  refine ⟨left, right, a, b, bodyA, bodyB, hres, ha, hb, hbodyA, hbodyB, hne, ?_⟩
  intro hmaskA hmaskB hsep
  have huni : UniformSlope S.signer.p S.signer.randomCount S.signer.enough V snapshot.world.other.family
      snapshot.world.other.hashTable (a.world.other.cipherHistory ++ b.world.other.cipherHistory) bodyA.1 bodyB.1 bodyA.2.1
      bodyB.2.1 a.signature.piop b.signature.piop bodyA.2.2.1 bodyB.2.2.1 := by
    rcases houtcome with huni | hmask | hmask
    · exact huni
    · exact absurd hmask hmaskA
    · exact absurd hmask hmaskB
  obtain ⟨reconL, reconR, auxD, pm, hsalt, hcorr, hplain, hrecL, hrecR, hpm, ⟨pa, hpa, hpa1⟩, hC, hall⟩ := huni
  refine ⟨reconL, reconR, pa, pm, hsalt, hrecL, hrecR, hC, hpa, by rw [hpa1]; exact hpm, ?_⟩
  intro full slopes
  -- A recorded seed collision at some execution, or the completions agree and the identities hold everywhere.
  by_cases hcol : ∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (ls rs : Spec.BAVC.Seed lambda),
      Spec.BAVCBinding.IsSeedCollision
        (induced (tau := tau) (kappa := kappa) snapshot.world.other.family snapshot.world.other.hashTable V.layout V.variant)
        bodyA.1 (Spec.SeedTree.leafOffset e i) ls rs ∧
      expandEntries snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) V.layout
        V.variant bodyA.1 (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) ls ∧
      expandEntries snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) V.layout
        V.variant bodyA.1 (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) rs
  · exact Or.inl hcol
  have hid : ∀ e a', masked pm.2 (slopes e) a' = bodyA.2.1.plain a' := by
    intro e a'
    rcases hall e (hsep e) with ⟨i, ls, rs, hseed, hentL, hentR⟩ | ⟨_, hident⟩
    · exact absurd ⟨e, i, ls, rs, hseed, hentL, hentR⟩ hcol
    · exact hident a'
  right
  rcases SlopeConsistencyLink.slopes_dichotomy pm.2 slopes bodyA.2.1.plain hid with hwin | hcommon
  · exact Or.inl hwin
  right
  let e0 : Fin tau := ⟨0, htau⟩
  have hcomm : ∀ e c', slopes e c' = slopes e0 c' := fun e c' => by rw [hcommon e e0]
  refine ⟨slopes e0, hcomm, fun hnz => ?_⟩
  -- Branch a's transcript: the candidate middle's values on its own table.
  obtain ⟨reconA, pa, pl, valueA, hrecA, _, hmidA, _, hrecovered⟩ :=
    CandidateSchemeChain.verify_evaluates _ _ _ V bodyA.1 bodyA.2.1 a.signature.piop bodyA.2.2.1 recA hevalA
  obtain ⟨hseedsA, _, _, _, _, hrevA⟩ :=
    CandidateBAVC.reconstruct_evaluates _ _ _ V.layout V.variant bodyA.1 _ bodyA.2.2.1.2 reconA hrecA
  have hagree : ∀ e i, i ≠ V.expand a.signature.piop bodyA.2.2.1.1 e → reconA.seeds e i = some (full e i) := by
    intro e i hi
    obtain ⟨seed, hseed, _, _⟩ := hrevA e i hi
    rw [hseedsA, hseed]
    show some seed = some (completion _ _ _ e i)
    rw [CandidateForkSlope.completion_self _ _ _ e i hi seed hseed]
  rw [hmid] at hmidA
  obtain ⟨_, _, hdelta, hwit, hrand, _⟩ := CandidateVerifier.candidateMiddle_evaluates S.signer.xi S.signer.p V.nodes encode
    S.signer.randomCount S.signer.enough bodyA.1 bodyA.2.1 _ reconA pa.1 full hagree _ _ _ valueA hmidA
  -- The accepted transcript's coefficient tuple.
  have hcoeffs' : Spec.CoefficientCompression.restoredCoefficients (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹
      (Spec.PIOPComposition.verifierRun widths S.hsize S.signer.xi (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹
        (S.expandBatching snapshot.input.payload.1).1 (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
        (fun j => algebraMap (ZMod 2) F (bodyA.2.1.witnessCorrection j) +
          (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * Spec.BLC.psi S.signer.xi
            (shareMatrix S.signer.p bodyA.1 full S.signer.randomCount S.signer.enough bodyA.2.1
              (V.expand a.signature.piop bodyA.2.2.1.1) (Spec.BLC.witnessIndex j)))
        (fun j => (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * Spec.BLC.psi S.signer.xi
          (shareMatrix S.signer.p bodyA.1 full S.signer.randomCount S.signer.enough bodyA.2.1
            (V.expand a.signature.piop bodyA.2.2.1.1) (Spec.BLC.randomnessIndex j))))
      bodyA.2.2.2 = snapshot.input.payload.2 := by
    rw [hcoeffs]
    simp only [Spec.SignatureComposition.verificationInput]
    rw [hrecovered]
    simp only [hdelta, ← hlinesA, hrecovered]
    congr 2 <;> funext j
    · exact (hwit j).symm
    · exact (hrand j).symm
  exact PIOPExtraction.difference_vanishes widths S.hsize S.signer.xi _ _ S.H' S.y S.signer.p bodyA.1 full
    S.signer.randomCount S.signer.enough bodyA.2.1 _ encode (slopes e0) hcomm hencode hnz
    bodyA.2.2.2 snapshot.input.payload.2 hcoeffs'

end
end SDitH.Proofs.ForkExtraction
