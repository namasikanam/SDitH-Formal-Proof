import SDitH.Spec.BLCArithmetic
import SDitH.Spec.ByteSampling
import SDitH.Spec.SeedPrimitives

/-! Algorithm 10 composed with Algorithms 7 and 5, the actual Gray folding,
byte sampling, consistency matrix expansion and line construction.

The primitive boundary consists of Enc*, the bit-string hash used by BAVC,
initialized PRG/XOF byte streams, and typed Hashaux/Hashlines calls. The latter
keep the source's component ordering while leaving its unspecified coefficient
serialization explicit. Byte consumption counts remain caller inputs as in
SampleFieldElements. No randomness, hash collision or PRG property is asserted.
-/

namespace SDitH.Spec.BLCCommit

open DomainSeparation

abbrev Digest (lambda : Nat) := Bits (2 * lambda)

structure AuxHashInput (lambda tau ell : Nat) where
  commitment : Digest lambda
  corrections : Fin (tau - 1) → Fin ell → ZMod 2

structure LinesHashInput (lambda tau kappa s wit : Nat) where
  auxiliary : Digest lambda
  plain : Fin s → ZMod 2
  base : Fin s → Fin tau → Fin kappa → ZMod 2
  witnessCorrection : Fin wit → ZMod 2

/-- Algorithm 10 line 25, keeping only the transmitted positive-index
corrections, then the plain consistency check and witness correction. -/
structure Auxiliary (tau s wit rnd : Nat) where
  corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2
  plain : Fin s → ZMod 2
  witnessCorrection : Fin wit → ZMod 2

structure Primitives (lambda tau kappa s wit rnd : Nat) where
  grinding : Grinding
  encStar : Bits lambda → Bits lambda → Bits lambda
  hash : List Bool → Digest lambda
  /-- Arguments: seed, salt, execution tweak, stream cursor. -/
  prg : Bits lambda → Bits lambda → Nat → Nat → Byte
  xof : Digest lambda → Nat → Byte
  hashAux : AuxHashInput lambda tau (s + (wit + rnd)) → Digest lambda
  hashLines : LinesHashInput lambda tau kappa s wit → Digest lambda

structure Result (F : Type*) [CommRing F] (lambda tau kappa s wit rnd : Nat) where
  witness : Fin wit → Polynomial F
  randomness : Fin rnd → Polynomial F
  lines : Digest lambda
  key : BAVC.Key lambda tau (2 ^ kappa)
  auxiliary : Auxiliary tau s wit rnd

def bitField (bit : Bool) : ZMod 2 := if bit then 1 else 0

def positiveIndex {tau : Nat} [NeZero tau] (j : Fin (tau - 1)) : Fin tau :=
  ⟨j.val + 1, by have hj := j.isLt; have ht := NeZero.ne tau; omega⟩

def positiveCorrections {tau ell : Nat} [NeZero tau]
    (corrections : Fin tau → Fin ell → ZMod 2) : Fin (tau - 1) → Fin ell → ZMod 2 :=
  fun j => corrections (positiveIndex j)

/-- The byte stream is initialized independently for each leaf seed and
execution tweak, exactly where Algorithm 10 calls PRG.Init. -/
def randomTable {lambda tau kappa s wit rnd : Nat}
    (p : Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (seeds : Fin tau → Fin (2 ^ kappa) → Bits lambda)
    (count : Nat) (enough : s + (wit + rnd) ≤ 8 * count) :
    Fin tau → Fin (2 ^ kappa) → Fin (s + (wit + rnd)) → ZMod 2 :=
  fun e i j => bitField ((ByteSampling.sampleBinary
    ⟨p.prg (seeds e i) salt e.val, 0⟩ (s + (wit + rnd)) count enough).value j)

/-- Algorithm 10 with all arithmetic and subroutine ordering explicit.
s=lambda+B is preserved in the type. Only the stated primitive/serialization
and byte-consumption boundaries remain inputs. -/
noncomputable def commit {F : Type*} [CommRing F] [Algebra (ZMod 2) F]
    {lambda tau kappa B wit rnd : Nat} [NeZero tau]
    (xi : F) (p : Primitives lambda tau kappa (lambda + B) wit rnd)
    (salt root : Bits lambda) (witness : Fin wit → ZMod 2)
    (randomCount consistencyCount : Nat)
    (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount) :
    Result F lambda tau kappa (lambda + B) wit rnd :=
  let bavc := BAVC.commit
    (SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash) salt root
  let random := randomTable p salt bavc.seeds randomCount hrandom
  let corrections := positiveCorrections (BLC.correction GrayCode.grayFieldRow random)
  let haux := p.hashAux ⟨bavc.hcom, corrections⟩
  let binaryMatrix := ByteSampling.expandConsistency (p.xof haux) lambda B
    (wit + rnd) consistencyCount hconsistency
  let M := fun i j => bitField (binaryMatrix.value i j)
  let arithmetic := BLC.commitArithmetic xi GrayCode.grayFieldRow random M witness
  { witness := arithmetic.witnessLines
    randomness := arithmetic.randomnessLines
    lines := p.hashLines ⟨haux, arithmetic.plainCheck, arithmetic.baseCheck, arithmetic.witnessCorrection⟩
    key := bavc.key
    auxiliary := ⟨corrections, arithmetic.plainCheck, arithmetic.witnessCorrection⟩ }

end SDitH.Spec.BLCCommit
