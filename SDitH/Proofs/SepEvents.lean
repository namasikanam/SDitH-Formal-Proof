import SDitH.Proofs.SlopeChainReduction
import SDitH.Proofs.ForkExtraction
import SDitH.Proofs.SolutionRegular
import SDitH.Proofs.EventRequirements

/-! Extraction from a fork with the hidden tuples separated at some
execution, in place of at every execution. The extracted slope is the first
branch's slope at a separated execution (with the seed array completed by
the second branch), the extracted witness is the corrections plus that
slope, and the extracted lines' slope coefficient is the psi image of the
first branch's share matrix less the extracted slope times the encoded
challenge, so that the first branch's candidate values are the lines at its
inverted challenge by construction. The non-separation event becomes the
agreement of the two tuples at every execution. The deterministic
extraction then needs only the first branch's acceptance: a winning fork
without the charged events is one of the prior events (mask after the fork,
full agreement, seed collision, mask trap, witnessed pair, unseen match,
zero challenge), the Schwartz–Zippel event, the batching event or the
solution event, where the last three carry the negations of the prior
events; the solver outputs the extracted witness. -/

namespace SDitH.Proofs.SepEvents

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SignatureQuerySelection Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.HashCipherEvaluation
open Spec.CandidateVerifier Spec.BLCSeedLines Spec.BLCSeedFold Spec.CandidateBAVC
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open BranchAccounting (MaskAfterCut)
open Spec.BAVC (Reconstructed)
open CandidateForkSlope (completion)
open CandidateReduction ForgeryReduction ExtractionSplit SimulatedSolver ForgeryEvents SlopeCoverFork EventRequirements
open PIOPExtraction (extractedWitness)
open SimulationGapCompat (EventOKP)
open Polynomial
open scoped Classical ENNReal

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

section Lines

variable {wit rnd : Nat}

/-- The extracted witness line of a coordinate, with an explicit slope coefficient. -/
def witnessLineM (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (u : Fin (s + (wit + rnd)) → ZMod 2)
    (m : Fin (s + (wit + rnd)) → F) (j : Fin wit) : F[X] :=
  C (algebraMap (ZMod 2) F (extractedWitness aux u j)) + C (m (Spec.BLC.witnessIndex j)) * X

/-- The extracted randomness line of a coordinate, with an explicit slope coefficient. -/
def randomnessLineM (u : Fin (s + (wit + rnd)) → ZMod 2) (m : Fin (s + (wit + rnd)) → F) (j : Fin rnd) : F[X] :=
  C (algebraMap (ZMod 2) F (u (Spec.BLC.randomnessIndex j))) + C (m (Spec.BLC.randomnessIndex j)) * X

omit [NeZero tau] [DecidableEq F] in
theorem witnessLineM_constant (aux : Spec.BLCCommit.Auxiliary tau s wit rnd) (u : Fin (s + (wit + rnd)) → ZMod 2)
    (m : Fin (s + (wit + rnd)) → F) (j : Fin wit) :
    (witnessLineM aux u m j).eval 0 = algebraMap (ZMod 2) F (extractedWitness aux u j) := by
  simp [witnessLineM]

end Lines

/-- The hidden tuples of the two branches differ at execution `e`. -/
def SepAt (a b : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths)
    (e : Fin tau) : Prop :=
  V.expand a.signature.piop bodyA.2.2.1.1 e ≠ V.expand b.signature.piop bodyB.2.2.1.1 e

/-- The two branches' hidden tuples agree at every execution. -/
def allAgree : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a b bodyA bodyB =>
    decide (∀ e, V.expand a.signature.piop bodyA.2.2.1.1 e = V.expand b.signature.piop bodyB.2.2.1.1 e)

/-- A separated execution when one exists, the first execution otherwise. -/
def sepIndex (htau : 0 < tau) (a b : Att F lambda tau kappa s higherCount w widths)
    (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths) : Fin tau :=
  if h : ∃ e, SepAt V a b bodyA bodyB e then Classical.choose h else ⟨0, htau⟩

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem sepIndex_sep (htau : 0 < tau) (a b : Att F lambda tau kappa s higherCount w widths)
    (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths) (h : ∃ e, SepAt V a b bodyA bodyB e) :
    SepAt V a b bodyA bodyB (sepIndex V htau a b bodyA bodyB) := by
  unfold sepIndex
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The extracted slope: the first branch's slope at the chosen execution,
with the seed array completed by the second branch. -/
def uOf (htau : 0 < tau) (a b : Att F lambda tau kappa s higherCount w widths)
    (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths) :
    Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 :=
  slopesOf S V a bodyA bodyB (sepIndex V htau a b bodyA bodyB)

/-- The extracted witness: the corrections plus the extracted slope. -/
def xOf (htau : 0 < tau) (a b : Att F lambda tau kappa s higherCount w widths)
    (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths) : Fin (selectorCount widths * w) → ZMod 2 :=
  extractedWitness bodyA.2.1 (uOf S V htau a b bodyA bodyB)

/-- The slope coefficient of the extracted lines: the psi image of the first
branch's share matrix at its hidden tuple, less the extracted slope times
the encoded challenge. -/
def mCoef (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau)
    (a b : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths)
    (c : Fin (s + (selectorCount widths * w + lambda * (widths.length - 1)))) : F :=
  Spec.BLC.psi S.signer.xi (shareMatrix S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough
      bodyA.2.1 (V.expand a.signature.piop bodyA.2.2.1.1) c) -
    algebraMap (ZMod 2) F (uOf S V htau a b bodyA bodyB c) * encode (V.expand a.signature.piop bodyA.2.2.1.1)

/-- The difference between the extracted lines' prover polynomial and the
hashed coefficient polynomial. -/
def differenceM (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau)
    (snapshot : Snap F lambda s higherCount w widths State)
    (a b : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths) :
    F[X] :=
  Spec.PIOPComposition.proverRun widths S.hsize S.signer.xi (S.expandBatching snapshot.input.payload.1).1
      (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
      (witnessLineM bodyA.2.1 (uOf S V htau a b bodyA bodyB) (mCoef S V encode htau a b bodyA bodyB))
      (randomnessLineM (uOf S V htau a b bodyA bodyB) (mCoef S V encode htau a b bodyA bodyB)) -
    Spec.CoefficientCompression.coefficientPolynomial snapshot.input.payload.2

omit [NeZero tau] [DecidableEq F] in
/-- The first branch's candidate values are the extracted lines at its
inverted challenge, by the definition of the slope coefficient. -/
theorem verifier_eq_lines (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau)
    (snapshot : Snap F lambda s higherCount w widths State)
    (a b : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths)
    (hnz : encode (V.expand a.signature.piop bodyA.2.2.1.1) ≠ 0) :
    Spec.PIOPComposition.verifierRun widths S.hsize S.signer.xi (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹
        (S.expandBatching snapshot.input.payload.1).1 (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
        (fun j => algebraMap (ZMod 2) F (bodyA.2.1.witnessCorrection j) +
          (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * Spec.BLC.psi S.signer.xi
            (shareMatrix S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1
              (V.expand a.signature.piop bodyA.2.2.1.1) (Spec.BLC.witnessIndex j)))
        (fun j => (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * Spec.BLC.psi S.signer.xi
          (shareMatrix S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1
            (V.expand a.signature.piop bodyA.2.2.1.1) (Spec.BLC.randomnessIndex j))) =
      (Spec.PIOPComposition.proverRun widths S.hsize S.signer.xi (S.expandBatching snapshot.input.payload.1).1
        (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
        (witnessLineM bodyA.2.1 (uOf S V htau a b bodyA bodyB) (mCoef S V encode htau a b bodyA bodyB))
        (randomnessLineM (uOf S V htau a b bodyA bodyB) (mCoef S V encode htau a b bodyA bodyB))).eval
          (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ := by
  rw [PIOPComposition.verifier_evaluates_prover]
  have h1 : (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * encode (V.expand a.signature.piop bodyA.2.2.1.1) = 1 :=
    inv_mul_cancel₀ hnz
  congr 1
  · funext j
    simp only [witnessLineM, extractedWitness, mCoef, eval_add, eval_mul, eval_C, eval_X, map_add]
    linear_combination (algebraMap (ZMod 2) F (uOf S V htau a b bodyA bodyB (Spec.BLC.witnessIndex j))) * h1
  · funext j
    simp only [randomnessLineM, mCoef, eval_add, eval_mul, eval_C, eval_X]
    linear_combination (algebraMap (ZMod 2) F (uOf S V htau a b bodyA bodyB (Spec.BLC.randomnessIndex j))) * h1

omit [NeZero tau] [DecidableEq F] in
/-- An accepting first branch: the difference polynomial vanishes at its
inverted challenge. -/
theorem differenceM_vanishes (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau)
    (snapshot : Snap F lambda s higherCount w widths State)
    (a b : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths)
    (hnz : encode (V.expand a.signature.piop bodyA.2.2.1.1) ≠ 0)
    (haccept : Spec.CoefficientCompression.restoredCoefficients (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹
      (Spec.PIOPComposition.verifierRun widths S.hsize S.signer.xi (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹
        (S.expandBatching snapshot.input.payload.1).1 (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
        (fun j => algebraMap (ZMod 2) F (bodyA.2.1.witnessCorrection j) +
          (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * Spec.BLC.psi S.signer.xi
            (shareMatrix S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1
              (V.expand a.signature.piop bodyA.2.2.1.1) (Spec.BLC.witnessIndex j)))
        (fun j => (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * Spec.BLC.psi S.signer.xi
          (shareMatrix S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1
            (V.expand a.signature.piop bodyA.2.2.1.1) (Spec.BLC.randomnessIndex j))))
      bodyA.2.2.2 = snapshot.input.payload.2) :
    (differenceM S V encode htau snapshot a b bodyA bodyB).eval (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ = 0 := by
  rw [verifier_eq_lines S V encode htau snapshot a b bodyA bodyB hnz] at haccept
  obtain ⟨_, hvalue⟩ := PIOPExtraction.restored_identity _ _ (inv_ne_zero hnz) bodyA.2.2.2 snapshot.input.payload.2 haccept
  unfold differenceM
  rw [eval_sub, hvalue, PIOPExtraction.coefficientPolynomial_eval, sub_self]

/-- The negations of the transferable prior events: mask after the fork,
full agreement, zero challenge. -/
def priorOK (encode : (Fin tau → Fin (2 ^ kappa)) → F) (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  !maskAfter snapshot result && !allAgree V result && !zeroChallenge V encode result

/-- The negations of the real-experiment prior events: seed collision, mask
trap, witnessed pair, unseen match. -/
def realOK (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  !seedCollision V snapshot result && !slopeTrap S V snapshot && !witnessedFork snapshot result && !unseenFork V snapshot result

/-- The Schwartz–Zippel event: without the prior events, a nonzero difference
polynomial vanishing at the first branch's inverted challenge. -/
def szPlus (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau) (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  priorOK V encode snapshot result && realOK S V snapshot result &&
    onAttempts (fun a b bodyA bodyB => decide (differenceM S V encode htau snapshot a b bodyA bodyB ≠ 0 ∧
      (differenceM S V encode htau snapshot a b bodyA bodyB).eval (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ = 0))
      result

/-- The batching event: without the prior events, a zero difference
polynomial with an extracted witness that is not a solution. -/
def batchingPlus (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau)
    (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  priorOK V encode snapshot result && realOK S V snapshot result &&
    onAttempts (fun a b bodyA bodyB => decide (differenceM S V encode htau snapshot a b bodyA bodyB = 0 ∧
      ¬ IsSolution S (xOf S V htau a b bodyA bodyB))) result

/-- The solution event: without the transferable prior events, a zero
difference polynomial with an extracted witness that is a solution. -/
def rsdSolvedPlus (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau)
    (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  priorOK V encode snapshot result &&
    onAttempts (fun a b bodyA bodyB => decide (differenceM S V encode htau snapshot a b bodyA bodyB = 0 ∧
      IsSolution S (xOf S V htau a b bodyA bodyB))) result

/-- The prior events. -/
def priorBad (encode : (Fin tau → Fin (2 ^ kappa)) → F) (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  maskAfter snapshot result || allAgree V result || seedCollision V snapshot result ||
    (slopeTrap S V snapshot || witnessedFork snapshot result || unseenFork V snapshot result) ||
    zeroChallenge V encode result

/-- A winning fork without the charged events is a prior event, the
Schwartz–Zippel event, the batching event or the solution event. -/
theorem good_implies_events (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support)
    (hgood : (forkWins snapshot.input result && !CandidateForkOutcome.forkBad (tau := tau) snapshot result) = true) :
    (priorBad S V encode snapshot result || szPlus S V encode htau snapshot result ||
      batchingPlus S V encode htau snapshot result || rsdSolvedPlus S V encode htau snapshot result) = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hgood
  obtain ⟨left, right, a, b, bodyA, bodyB, recA, recB, hres, ha, hb, hbodyA, hbodyB, _, hevalA, _, hlinesA, _, hcoeffs, _⟩ :=
    CandidateForkOutcome.fork_good_outcome S V verifyBudget publicKey sampleWitness adversary hlambda htau S.signer.xi
      S.signer.p encode S.signer.randomCount S.signer.enough hmid hencoding hlinesEnc index fuel c hc snapshot hsnap result hr
      hgood.1 hgood.2
  subst hres
  by_cases hpb : priorBad S V encode snapshot (some (left, right)) = true
  · simp [hpb]
  simp only [Bool.not_eq_true] at hpb
  rw [hpb, Bool.false_or]
  have hpb' := hpb
  simp only [priorBad, Bool.or_eq_false_iff] at hpb'
  obtain ⟨⟨⟨⟨hmask, hagree⟩, hcoll⟩, ⟨⟨htrap, hwit⟩, hunseen⟩⟩, hzero⟩ := hpb'
  have hok : priorOK V encode snapshot (some (left, right)) = true := by
    simp [priorOK, hmask, hagree, hzero]
  have hrok : realOK S V snapshot (some (left, right)) = true := by
    simp [realOK, hcoll, htrap, hwit, hunseen]
  have hnz : encode (V.expand a.signature.piop bodyA.2.2.1.1) ≠ 0 := by
    simp only [zeroChallenge, onAttempts, ha, hb, hbodyA, hbodyB, decide_eq_false_iff_not] at hzero
    exact hzero
  -- The first branch's acceptance gives the vanishing of the difference polynomial.
  obtain ⟨reconA, pa, pl, valueA, hrecA, _, hmidA, _, hrecovered⟩ :=
    CandidateSchemeChain.verify_evaluates _ _ _ V bodyA.1 bodyA.2.1 a.signature.piop bodyA.2.2.1 recA hevalA
  obtain ⟨hseedsA, _, _, _, _, hrevA⟩ :=
    CandidateBAVC.reconstruct_evaluates _ _ _ V.layout V.variant bodyA.1 _ bodyA.2.2.1.2 reconA hrecA
  have hagreeA : ∀ e i, i ≠ V.expand a.signature.piop bodyA.2.2.1.1 e →
      reconA.seeds e i = some (fullOf V a bodyA bodyB e i) := by
    intro e i hi
    obtain ⟨seed, hseed, _, _⟩ := hrevA e i hi
    rw [hseedsA, hseed]
    show some seed = some (completion _ _ _ e i)
    rw [CandidateForkSlope.completion_self _ _ _ e i hi seed hseed]
  rw [hmid] at hmidA
  obtain ⟨_, _, hdelta, hwitv, hrand, _⟩ := CandidateVerifier.candidateMiddle_evaluates S.signer.xi S.signer.p V.nodes encode
    S.signer.randomCount S.signer.enough bodyA.1 bodyA.2.1 _ reconA pa.1 (fullOf V a bodyA bodyB) hagreeA _ _ _ valueA hmidA
  have hcoeffs' : Spec.CoefficientCompression.restoredCoefficients (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹
      (Spec.PIOPComposition.verifierRun widths S.hsize S.signer.xi (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹
        (S.expandBatching snapshot.input.payload.1).1 (S.expandBatching snapshot.input.payload.1).2 S.H' S.y
        (fun j => algebraMap (ZMod 2) F (bodyA.2.1.witnessCorrection j) +
          (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * Spec.BLC.psi S.signer.xi
            (shareMatrix S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1
              (V.expand a.signature.piop bodyA.2.2.1.1) (Spec.BLC.witnessIndex j)))
        (fun j => (encode (V.expand a.signature.piop bodyA.2.2.1.1))⁻¹ * Spec.BLC.psi S.signer.xi
          (shareMatrix S.signer.p bodyA.1 (fullOf V a bodyA bodyB) S.signer.randomCount S.signer.enough bodyA.2.1
            (V.expand a.signature.piop bodyA.2.2.1.1) (Spec.BLC.randomnessIndex j))))
      bodyA.2.2.2 = snapshot.input.payload.2 := by
    rw [hcoeffs]
    simp only [Spec.SignatureComposition.verificationInput]
    rw [hrecovered]
    simp only [hdelta, ← hlinesA, hrecovered]
    congr 2 <;> funext j
    · exact (hwitv j).symm
    · exact (hrand j).symm
  have hvan := differenceM_vanishes S V encode htau snapshot a b bodyA bodyB hnz hcoeffs'
  simp only [szPlus, batchingPlus, rsdSolvedPlus, hok, hrok, onAttempts, ha, hb, hbodyA, hbodyB, Bool.true_and,
    Bool.or_eq_true, decide_eq_true_eq]
  by_cases hD : differenceM S V encode htau snapshot a b bodyA bodyB = 0
  · by_cases hsol : IsSolution S (xOf S V htau a b bodyA bodyB)
    · exact Or.inr ⟨hD, hsol⟩
    · exact Or.inl (Or.inr ⟨hD, hsol⟩)
  · exact Or.inl (Or.inl ⟨hD, hvan⟩)

/-- The union of the prior events, the Schwartz–Zippel event, the batching
event and the solution event. -/
def unionEvent (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau)
    (snapshot : Snap F lambda s higherCount w widths State)
    (result : Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths)) : Bool :=
  priorBad S V encode snapshot result || szPlus S V encode htau snapshot result ||
    batchingPlus S V encode htau snapshot result || rsdSolvedPlus S V encode htau snapshot result

/-- The fork experiment's success is at most the union event plus the
charged-event bound. -/
theorem fork_le_union (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (index fuel : Nat) :
    (forkExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEvent S V encode htau) index fuel) true +
      (fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))) +
      fuel * (epsilonC lambda bound (fuel * (bound + bound)) + epsilonC lambda bound (fuel * (bound + bound))) +
      (2 : ℝ≥0∞) * (fuel * (bound * digestInv lambda + bound * digestInv lambda) +
        fuel * (epsilonM lambda tau bound (fuel * (bound + bound)) + epsilonM lambda tau bound (fuel * (bound + bound))))) := by
  have hmono : (CandidateForkOutcome.goodForkExperiment S V verifyBudget publicKey sampleWitness adversary index fuel) true ≤
      (eventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEvent S V encode htau) index fuel) true := by
    unfold CandidateForkOutcome.goodForkExperiment eventExperiment
    refine bind_true_mono _ _ _ fun c hc => ?_
    cases c with
    | ended terminal => exact le_rfl
    | saved snapshot =>
      refine map_true_mono_support _ _ _ fun result hr hgood => ?_
      exact good_implies_events S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc
        index fuel _ hc snapshot rfl result hr hgood
  exact (CandidateForkOutcome.forkExperiment_split S V verifyBudget publicKey sampleWitness adversary index fuel).trans
    (add_le_add hmono (CandidateForkOutcome.forkBad_bound S V verifyBudget publicKey sampleWitness adversary bound hcommit
      hverify hone index fuel))

/-- The random-index fork experiment is at most the random-index union
event plus the charged-event bound. -/
theorem random_fork_le_union (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) :
    (randomForkExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary fuel) true ≤
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEvent S V encode htau) fuel) true +
      ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
          epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
      (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) + epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
      (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
        (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
          epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) := by
  rw [randomForkExperiment_eq]
  unfold randomEventExperiment
  refine bind_true_le_add_const _ _ _ _ fun index _ => ?_
  have h := fork_le_union S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding hlinesEnc bound
    hcommit hverify hone index.val (fuel + 1)
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The forgery skeleton: the forger's advantage against the events. -/
theorem forgery_le_events (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => allAgree V) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true +
      ((randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot _ => slopeTrap S V snapshot) fuel) true +
        (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => witnessedFork snapshot) fuel) true +
        (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => unseenFork V snapshot) fuel) true) +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (szPlus S V encode htau) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (batchingPlus S V encode htau) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (rsdSolvedPlus S V encode htau) fuel) true +
      ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
          epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
      (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) + epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
      (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
        (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
          epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  have hfork := SignatureForgeryFork.forgery_to_fork (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)
    adversary fuel
  have hunion := random_fork_le_union S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
    hlinesEnc bound hcommit hverify hone fuel
  have hsplit : (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (unionEvent S V encode htau) fuel) true ≤
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary maskAfter fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => allAgree V) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true +
      ((randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot _ => slopeTrap S V snapshot) fuel) true +
        (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => witnessedFork snapshot) fuel) true +
        (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun snapshot => unseenFork V snapshot) fuel) true) +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (fun _ => zeroChallenge V encode) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (szPlus S V encode htau) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (batchingPlus S V encode htau) fuel) true +
      (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (rsdSolvedPlus S V encode htau) fuel) true := by
    unfold unionEvent
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    unfold priorBad
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add_left ?_ _
    refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
    refine add_le_add ?_ ?_
    · refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
      refine add_le_add_left ?_ _
      exact randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel
    · refine (randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel).trans ?_
      refine add_le_add_left ?_ _
      exact randomEventExperiment_or_le S V verifyBudget publicKey sampleWitness adversary _ _ fuel
  refine hfork.trans (mul_le_mul_right ?_ _)
  refine add_le_add_left ?_ _
  refine hunion.trans (add_le_add_left ?_ _)
  refine hsplit.trans (le_of_eq ?_)
  ring

section Requirements

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The full-agreement event's requirements. -/
theorem eventOKP_allAgree :
    EventOKP (fun (_ : Snap F lambda s higherCount w widths State) => allAgree V) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => rfl) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

omit [NeZero tau] in
/-- The solution event's requirements. -/
theorem eventOKP_rsdSolvedPlus (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau) :
    EventOKP (higherCount := higherCount) (w := w) (widths := widths) (State := State) (rsdSolvedPlus S V encode htau) := by
  refine eventOKP_of _ (fun _ => rfl) (fun sn g H res => ?_) (fun sn a t w₀ f H b₁ b₂ right => ?_)
    (fun sn left t w₀ f H b₁ b₂ a' => ?_)
  · rfl
  · rcases right with ⟨a', ⟨tr, b₁', b₂'⟩⟩
    cases t <;> cases tr <;> rfl
  · rcases left with ⟨a, ⟨tl, b₁', b₂'⟩⟩
    cases tl <;> cases t <;> rfl

end Requirements

section Solver

variable (sim : Scheme (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
    (Signature (Spec.BAVC.Digest lambda) (Option (Bod F lambda tau kappa s higherCount w widths)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
    (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))

/-- The solver's output on a fork result: the extracted witness. -/
def solverOutput (htau : 0 < tau) (_snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) →
      Option (Fin (selectorCount widths * w) → ZMod 2)
  | none => none
  | some (l, r) =>
    match l.checked.terminal, r.checked.terminal with
    | .attempt a, .attempt b =>
      match a.signature.body, b.signature.body with
      | some bodyA, some bodyB => some (xOf S V htau a b bodyA bodyB)
      | _, _ => none
    | _, _ => none

/-- The solver: the fork experiment of the scheme at a random index with the
extracted output. -/
def solver (htau : 0 < tau) (fuel : Nat) : PMF (Option (Fin (selectorCount widths * w) → ZMod 2)) :=
  (PMF.uniformOfFintype (Fin (fuel + 1))).bind fun index =>
    (cutExperiment sim adversary index.val (fuel + 1)).bind fun c => match c with
      | .ended _ => PMF.pure none
      | .saved snapshot => (forkAt sim adversary snapshot).map (solverOutput S V htau snapshot)

/-- The solver's success: its output is a solution of the public instance. -/
def solverSuccess (htau : 0 < tau) (fuel : Nat) : ℝ≥0∞ :=
  ((solver S V adversary sim htau fuel).map fun out => decide (∃ bits, out = some bits ∧ IsSolution S bits)) true

omit [NeZero tau] in
theorem rsdSolvedPlus_output (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau)
    (snapshot : Snap F lambda s higherCount w widths State) (result)
    (h : rsdSolvedPlus S V encode htau snapshot result = true) :
    ∃ bits, solverOutput S V htau snapshot result = some bits ∧ IsSolution S bits := by
  rcases result with _ | ⟨l, r⟩
  · exact absurd h (by simp [rsdSolvedPlus, onAttempts])
  unfold rsdSolvedPlus at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  unfold onAttempts at h
  dsimp only at h
  split at h
  · rename_i a b ha hb
    split at h
    · rename_i bodyA bodyB hbodyA hbodyB
      obtain ⟨_, hsol⟩ := decide_eq_true_eq.mp h
      refine ⟨xOf S V htau a b bodyA bodyB, ?_, hsol⟩
      simp only [solverOutput, ha, hb, hbodyA, hbodyB]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [NeZero tau] in
/-- The solution event is at most the solver's success. -/
theorem solverSuccess_ge (encode : (Fin tau → Fin (2 ^ kappa)) → F) (htau : 0 < tau) (fuel : Nat) :
    (simEventExperiment adversary sim (rsdSolvedPlus S V encode htau) fuel) true ≤
      solverSuccess S V adversary sim htau fuel := by
  unfold solverSuccess solver simEventExperiment
  rw [PMF.map_bind]
  refine bind_true_mono _ _ _ fun index _ => ?_
  rw [PMF.map_bind]
  refine bind_true_mono _ _ _ fun c _ => ?_
  cases c with
  | ended terminal => simp
  | saved snapshot =>
    rw [PMF.map_comp]
    refine ForkCutRun.map_true_mono _ _ _ fun result h => ?_
    obtain ⟨bits, hout, hsol⟩ := rsdSolvedPlus_output S V encode htau snapshot result h
    simp only [Function.comp, decide_eq_true_eq]
    exact ⟨bits, hout, hsol⟩

end Solver

/-- The solver's output is a weight-`w` solution of the public instance. -/
def rsdSuccess (htau : 0 < tau) (fuel : Nat) : ℝ≥0∞ :=
  ((solver S V adversary (Spec.CandidateSimulator.simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel).map
    fun out => decide (∃ bits, out = some bits ∧
      Spec.SDSolution (Spec.KeyGeneration.instanceOf S.H' S.y) w
        (SolutionRegular.solutionVector widths S.hsize bits))) true

/-- The solver's success on the mux residual is at most its syndrome-decoding
success. -/
theorem solverSuccess_le_rsd (htau : 0 < tau) (fuel : Nat) :
    solverSuccess S V adversary (Spec.CandidateSimulator.simulatedScheme S V verifyBudget publicKey sampleWitness) htau fuel ≤
      rsdSuccess S V verifyBudget publicKey sampleWitness adversary htau fuel := by
  unfold solverSuccess rsdSuccess
  refine ForkCutRun.map_true_mono _ _ _ fun out h => ?_
  obtain ⟨bits, hout, hsol⟩ := of_decide_eq_true h
  exact decide_eq_true ⟨bits, hout, SolutionRegular.isSolution_sd widths S bits hsol⟩

end
end SDitH.Proofs.SepEvents
