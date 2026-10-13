import SDitH.Spec.SignatureComposition
import SDitH.Proofs.PIOPComposition
import SDitH.Proofs.CoefficientCompression
import SDitH.Proofs.BLCRetry

namespace SDitH.Proofs.SignatureComposition

open Spec.SignatureComposition Spec.DomainSeparation Spec.PIOPArithmetic
open Spec.CoefficientCompression Spec.Batching
open Polynomial

variable {F Aux : Type*} [Field F]

/-- A returned signing observation contains a real Algorithm-11 return;
the signature is assembled from that exact counter and opening. -/
theorem signing_returned_iff [DecidableEq F] {lambda tau N wpow higherCount : Nat}
    (prepared : Prepared F Aux lambda tau N higherCount) (Topen : Nat)
    (expandEvaluation : Digest lambda → Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau N wpow)
    (encode : (Fin tau → Fin N) → F) (fuel : Nat)
    (counter : Spec.BLCRetry.Counter) (signature : Signature F Aux lambda tau higherCount) :
    observeSigning prepared Topen expandEvaluation encode fuel = .returned counter signature ↔
      ∃ opening, Spec.BLCRetry.openRandomEvaluation prepared.key Topen
        (expandEvaluation prepared.piop) encode fuel = .returned counter opening ∧
        signature = attachOpening prepared counter opening := by
  unfold observeSigning
  cases h : Spec.BLCRetry.openRandomEvaluation prepared.key Topen
      (expandEvaluation prepared.piop) encode fuel with
  | pending next => simp
  | undefined fault => simp
  | returned ctr opening =>
    simp [eq_comm]
    intro hc
    subst ctr
    rfl

/-- Every actual signing return carries a successful BAVC opening and a
nonzero merged header challenge. This does not assert that Algorithm 12's later
reconstruction succeeds or reproduces the committed line digest. -/
theorem signing_returned_header [DecidableEq F] {lambda tau N wpow higherCount : Nat}
    (prepared : Prepared F Aux lambda tau N higherCount) (Topen : Nat)
    (expandEvaluation : Digest lambda → Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau N wpow)
    (encode : (Fin tau → Fin N) → F) (fuel : Nat)
    (counter : Spec.BLCRetry.Counter) (signature : Signature F Aux lambda tau higherCount)
    (h : observeSigning prepared Topen expandEvaluation encode fuel = .returned counter signature) :
    signature.decomposition.1 = counter ∧ signature.piop = prepared.piop ∧
      Spec.BLCRetry.checkEvaluationHeader (expandEvaluation prepared.piop) encode counter =
        some (encode (expandEvaluation prepared.piop counter).hidden)⁻¹ ∧
      (encode (expandEvaluation prepared.piop counter).hidden)⁻¹ ≠ 0 ∧
      Spec.BAVC.openCommitment prepared.key (expandEvaluation prepared.piop counter).hidden Topen =
        .ok signature.decomposition.2 := by
  obtain ⟨opening, hopen, rfl⟩ := (signing_returned_iff prepared Topen expandEvaluation encode
    fuel counter signature).mp h
  obtain ⟨hheader, hnonzero, hbavc⟩ := BLCRetry.returned_header_and_opening prepared.key Topen
    (expandEvaluation prepared.piop) encode fuel counter opening hopen
  exact ⟨rfl, rfl, hheader, inv_ne_zero hnonzero, hbavc⟩

section Coefficients

variable [Algebra (ZMod 2) F]
variable {r k w lambda tau N higherCount : Nat}
variable (widths : List Nat) (hdegree : widths.length = higherCount + 1)
variable (hsize : leafCount widths * w = r + k) (xi : F)
variable (expandBatching : Digest lambda → (Fin (blockCount r lambda) → F) × (Fin w → F))
variable (hashPiop : HashInput F lambda higherCount → Digest lambda)
variable (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
variable (publicKey message : List Bool) (salt : Bits lambda)
variable (commit : Commitment F Aux lambda tau N (selectorCount widths * w)
  (lambda * (widths.length - 1)))

/-- These are the mathematical evaluations of the committed arrays. The
definition asserts nothing about what BLC.RecomputeEvaluation actually returns. -/
noncomputable def evaluatedCommitment (delta : F) :
    Recomputed F lambda (selectorCount widths * w) (lambda * (widths.length - 1)) :=
  ⟨delta, fun j => (commit.witness j).eval delta,
    fun j => (commit.randomness j).eval delta, commit.lines⟩

theorem prepared_degree (hd : 2 ≤ widths.length)
    (hw : ∀ j, (commit.witness j).natDegree ≤ 1)
    (hr : ∀ j, (commit.randomness j).natDegree ≤ 1) :
    (prepare widths hdegree hsize xi expandBatching hashPiop H' y publicKey message salt commit).polynomial.natDegree ≤
      higherCount + 1 := by
  simpa only [prepare, ← hdegree] using PIOPComposition.prover_degree widths hsize hd xi
    (expandBatching commit.lines).1 (expandBatching commit.lines).2 H' y commit.witness commit.randomness hw hr

theorem verification_input_on_evaluations (counter : Spec.BLCRetry.Counter)
    (opening : Spec.BAVC.Opening lambda tau) (delta : F) :
    let prepared := prepare widths hdegree hsize xi expandBatching hashPiop H' y publicKey message salt commit
    verificationInput widths hdegree hsize xi expandBatching H' y publicKey message
      (attachOpening prepared counter opening) (evaluatedCommitment widths commit delta) =
      ⟨publicKey, commit.lines,
        restoredCoefficients delta (prepared.polynomial.eval delta) prepared.higher, message⟩ := by
  dsimp only [prepare, verificationInput, attachOpening, evaluatedCommitment]
  rw [← PIOPComposition.verifier_evaluates_prover]

/-- Even on exact committed evaluations, the signing and verification hash
tuples agree precisely when the actual computed constant coefficient vanishes.
The statement is about typed inputs, without presuming injective serialization
or asserting that unequal inputs produce unequal hash outputs. -/
theorem verification_input_eq_iff (counter : Spec.BLCRetry.Counter)
    (opening : Spec.BAVC.Opening lambda tau) (delta : F) (hdelta : delta ≠ 0)
    (hd : 2 ≤ widths.length)
    (hw : ∀ j, (commit.witness j).natDegree ≤ 1)
    (hr : ∀ j, (commit.randomness j).natDegree ≤ 1) :
    let prepared := prepare widths hdegree hsize xi expandBatching hashPiop H' y publicKey message salt commit
    verificationInput widths hdegree hsize xi expandBatching H' y publicKey message
      (attachOpening prepared counter opening) (evaluatedCommitment widths commit delta) =
      ⟨publicKey, commit.lines, hashedCoefficients higherCount prepared.polynomial, message⟩ ↔
      prepared.polynomial.coeff 0 = 0 := by
  dsimp only
  rw [verification_input_on_evaluations]
  have hp := prepared_degree widths hdegree hsize xi expandBatching hashPiop H' y publicKey message salt commit hd hw hr
  have he := CoefficientCompression.restored_eq_hashed_iff higherCount _ hp delta hdelta
  constructor
  · intro h
    exact he.mp (congrArg HashInput.coefficients h)
  · intro h
    congr 1
    exact he.mpr h

/-- Local composition correctness given exact committed evaluations and an
actually zero constant term. These explicit conditions are not a theorem about
the currently inconsistent BLC reconstruction or source witness encoding. -/
theorem verify_on_evaluations (counter : Spec.BLCRetry.Counter)
    (opening : Spec.BAVC.Opening lambda tau) (delta : F) (hdelta : delta ≠ 0)
    (hd : 2 ≤ widths.length)
    (hw : ∀ j, (commit.witness j).natDegree ≤ 1)
    (hr : ∀ j, (commit.randomness j).natDegree ≤ 1)
    (hzero : (prepare widths hdegree hsize xi expandBatching hashPiop H' y publicKey message salt commit).polynomial.coeff 0 = 0) :
    let prepared := prepare widths hdegree hsize xi expandBatching hashPiop H' y publicKey message salt commit
    verifyPostRecompute widths hdegree hsize xi expandBatching hashPiop H' y publicKey message
      (attachOpening prepared counter opening) (some (evaluatedCommitment widths commit delta)) = true := by
  have he := (verification_input_eq_iff widths hdegree hsize xi expandBatching hashPiop H' y publicKey message
    salt commit counter opening delta hdelta hd hw hr).mpr hzero
  dsimp only
  simp only [verifyPostRecompute, decide_eq_true_eq]
  rw [he]
  rfl

end Coefficients
end SDitH.Proofs.SignatureComposition
