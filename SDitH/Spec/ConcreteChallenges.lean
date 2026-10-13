import SDitH.Spec.IntegerSamplingVector
import SDitH.Spec.CipherGrinding
import SDitH.Spec.CipherPrimitives
import SDitH.Spec.FieldBytes
import SDitH.Spec.Batching

/-! The §3.2.2 challenge subroutines with the actual SHAKE and Enc* bodies.
Counter serialization/MapToBits and extension-field byte ordering stay explicit.
Hash grinding uses the actual full integer sampler, whose missing B binding is
not repaired. Cipher grinding is staged at its undocumented material parse and
one-subscript Extract operation. Later stages do not supply their own inputs
as if those gaps had been resolved. No concrete-XOF uniformity is assumed.
-/

namespace SDitH.Spec.ConcreteChallenges

open DomainSeparation FieldRepresentation ByteSampling

abbrev CounterEncoding := BLCRetry.Counter → Bits 32

/-- Fixed-width concatenation for XOF.Init(hpiop, ctr), preserving argument
order. The counter's bit order is a supplied representation boundary. -/
def evaluationInput {lambda : Nat} (encodeCounter : CounterEncoding)
    (digest : Bits (2 * lambda)) (counter : BLCRetry.Counter) : List Bool :=
  List.ofFn digest ++ List.ofFn (encodeCounter counter)

def cipherInput {lambda : Nat} (encodeCounter : CounterEncoding)
    (digest : Bits (2 * lambda)) (counter : BLCRetry.Counter)
    (ciphertexts : Bits lambda × Bits lambda) : List Bool :=
  evaluationInput encodeCounter digest counter ++ List.ofFn ciphertexts.1 ++ List.ofFn ciphertexts.2

inductive EvaluationObservation (tau kappa wpow : Nat) where
  | pending (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
  | undefinedIntegerAssignment (state : IntegerSampling.PartialVector (2 ^ kappa) tau)
      (candidate : IntegerSampling.Candidate)
  | returned (value : BLCRetry.Challenge tau (2 ^ kappa) wpow) (next : Reader)

/-- Hash-grinding lines 3–4 follow the integer loop's actual returned cursor.
The grinding call is never run from a pending or undefined integer result. -/
def finishHash {tau kappa wpow : Nat} (count : Nat) (enough : wpow ≤ 8 * count)
    (integers : IntegerSampling.VectorObservation (2 ^ kappa) tau) :
    EvaluationObservation tau kappa wpow :=
  match integers with
  | .pending state => .pending state
  | .undefinedAssignment state candidate => .undefinedIntegerAssignment state candidate
  | .returned values next =>
    let grinding := sampleBinary next wpow count enough
    .returned ⟨(fun e => values[e]), grinding.value⟩ grinding.next

def hashEvaluationWithBinding (category : Category) (tau kappa wpow : Nat)
    (encodeCounter : CounterEncoding) (digest : Bits (2 * width category))
    (counter : BLCRetry.Counter) (integerBinding : Option Nat)
    (fuel grindingCount : Nat) (enough : wpow ≤ 8 * grindingCount) :
    EvaluationObservation tau kappa wpow :=
  let src := SHAKE.reader category (evaluationInput encodeCounter digest counter)
  finishHash grindingCount enough (IntegerSampling.sampleVectorWithBinding
    (2 ^ kappa) (pow_pos (by decide) _) tau integerBinding fuel src)

/-- The literal hash-grinding subroutine, leaving B undeclared. -/
def hashEvaluation (category : Category) (tau kappa wpow : Nat)
    (encodeCounter : CounterEncoding) (digest : Bits (2 * width category))
    (counter : BLCRetry.Counter) (fuel grindingCount : Nat) (enough : wpow ≤ 8 * grindingCount) :
    EvaluationObservation tau kappa wpow :=
  hashEvaluationWithBinding category tau kappa wpow encodeCounter digest counter none
    fuel grindingCount enough

/-- Lines 1–2 read exactly the printed 4*lambda bytes. A parse into the four
required windows is not chosen. `next` records actual consumed-byte position. -/
def readCipherMaterial (category : Category) (encodeCounter : CounterEncoding)
    (digest : Bits (2 * width category)) (counter : BLCRetry.Counter) :
    Result (Fin (4 * width category) → Byte) :=
  let src := SHAKE.reader category (evaluationInput encodeCounter digest counter)
  ⟨readBytes src (4 * width category), advance src (4 * width category)⟩

structure ExtractionBoundary (lambda : Nat) where
  ciphertexts : Bits lambda × Bits lambda
  xorValue : Bits lambda

/-- Lines 3–9 after an explicitly supplied material parse. Counter MapToBits
is separate from the counter's XOF serialization; no equality is imposed.
The output stops before the unspecified Extract_(wpow-1) operation. -/
def cipherAfterMaterial (category : Category) (mapCounter : CounterEncoding)
    (counter : BLCRetry.Counter) (material : CipherGrinding.Material (width category)) :
    ExtractionBoundary (width category) :=
  let ciphertexts := CipherGrinding.cipherCalls (CipherPrimitives.encStar category)
    (mapCounter counter) material
  ⟨ciphertexts, CipherGrinding.xorCiphertexts ciphertexts⟩

def finishCipher {tau kappa wpow : Nat} (grinding : Bits wpow)
    (integers : IntegerSampling.VectorObservation (2 ^ kappa) tau) :
    EvaluationObservation tau kappa wpow :=
  match integers with
  | .pending state => .pending state
  | .undefinedAssignment state candidate => .undefinedIntegerAssignment state candidate
  | .returned values next => .returned ⟨(fun e => values[e]), grinding⟩ next

/-- Lines 11–13 after explicitly supplied extraction output. The XOF is
reinitialized, not continued from the material reader. No zero-grinding shortcut
is added from the conflicting prose: the printed index loop is always invoked. -/
def cipherAfterExtraction (category : Category) (tau kappa wpow : Nat)
    (encodeCounter : CounterEncoding) (digest : Bits (2 * width category))
    (counter : BLCRetry.Counter) (state : ExtractionBoundary (width category))
    (grinding : Bits wpow) (integerBinding : Option Nat) (fuel : Nat) :
    EvaluationObservation tau kappa wpow :=
  let src := SHAKE.reader category (cipherInput encodeCounter digest counter state.ciphertexts)
  finishCipher grinding (IntegerSampling.sampleVectorWithBinding
    (2 ^ kappa) (pow_pos (by decide) _) tau integerBinding fuel src)

/-- The actual SHAKE batching routine and exact Table-2 coefficient decoder.
The ceil((n-k)/lambda) count is instantiated as blockCount r lambda. Byte order
and both sufficient consumption counts remain explicit source boundaries. -/
noncomputable def batching (category : Category) (order : FieldBytes.ByteOrder category)
    (r w count₁ count₂ : Nat)
    (enough₁ : Batching.blockCount r (width category) * FieldBytes.byteCount category ≤ count₁)
    (enough₂ : w * FieldBytes.byteCount category ≤ count₂)
    (digest : Bits (2 * width category)) : Result
      ((Fin (Batching.blockCount r (width category)) → QuotientRing category) ×
        (Fin w → QuotientRing category)) :=
  FieldBytes.expandBatching category order (HashPrimitives.digestXOF category digest)
    (Batching.blockCount r (width category)) w count₁ count₂ enough₁ enough₂

end SDitH.Spec.ConcreteChallenges
