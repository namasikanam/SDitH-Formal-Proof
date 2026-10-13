import SDitH.Spec.ConcreteChallenges

/-! The complete staged cipher-based ExpandEvaluationChallenge, printed p. 19.
Source-resolution boundaries are explicit optional functions, not security
contracts or chosen defaults. An absent interpretation is an undefined source
operation, never an ordinary challenge rejection. Actual SHAKE/Enc* computations
and the full integer sampler are retained between those boundaries.
-/

namespace SDitH.Spec.CipherEvaluation

open DomainSeparation FieldRepresentation ByteSampling ConcreteChallenges

abbrev MaterialParser (category : Category) :=
  (Fin (4 * width category) → Byte) → CipherGrinding.Material (width category)

structure Bindings (category : Category) (wpow : Nat) where
  materialParser : Option (MaterialParser category)
  counterMap : Option CounterEncoding
  extraction : Option (Bits (width category) → Bits wpow)
  integerValue : Option Nat

/-- No material parse, MapToBits order, Extract convention, or B=v repair
is selected for the literal source. XOF counter serialization is still an
explicit input, as in the hash-based expansion. -/
def absentBindings (category : Category) (wpow : Nat) : Bindings category wpow :=
  ⟨none, none, none, none⟩

inductive Boundary (lambda : Nat) where
  | materialParse (raw : Result (Fin (4 * lambda) → Byte))
  | counterMap (material : CipherGrinding.Material lambda)
  | extraction (state : ExtractionBoundary lambda)

/-- After the line-2 material parse, stop at the first unresolved operation.
The counterMap payload retains the inputs to the already-defined key slices.
Extract takes the actual xor, not freely supplied grinding bits. -/
def afterParsed (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : BLCRetry.Counter) (bindings : Bindings category wpow)
    (material : CipherGrinding.Material (width category)) (fuel : Nat) :
    Except (Boundary (width category)) (EvaluationObservation tau kappa wpow) :=
  match bindings.counterMap with
  | none => .error (.counterMap material)
  | some mapping =>
    let state := cipherAfterMaterial category mapping counter material
    match bindings.extraction with
    | none => .error (.extraction state)
    | some extract => .ok (cipherAfterExtraction category tau kappa wpow encoding digest counter
        state (extract state.xorValue) bindings.integerValue fuel)

/-- All thirteen printed lines in source order, with explicit source gaps.
Fuel only observes the final integer loop; even fuel zero performs the preceding
finite computations. The initial SHAKE input still includes the counter.
No all-zero-grinding shortcut removes lines 11–12. -/
def evaluateWithBindings (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : BLCRetry.Counter) (bindings : Bindings category wpow) (fuel : Nat) :
    Except (Boundary (width category)) (EvaluationObservation tau kappa wpow) :=
  let raw := readCipherMaterial category encoding digest counter
  match bindings.materialParser with
  | none => .error (.materialParse raw)
  | some parse => afterParsed category tau kappa wpow encoding digest counter bindings
      (parse raw.value) fuel

def evaluate (category : Category) (tau kappa wpow : Nat)
    (encoding : CounterEncoding) (digest : Bits (2 * width category))
    (counter : BLCRetry.Counter) (fuel : Nat) :
    Except (Boundary (width category)) (EvaluationObservation tau kappa wpow) :=
  evaluateWithBindings category tau kappa wpow encoding digest counter
    (absentBindings category wpow) fuel

end SDitH.Spec.CipherEvaluation
