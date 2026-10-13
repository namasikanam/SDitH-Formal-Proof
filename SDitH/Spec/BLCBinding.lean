import SDitH.Spec.BAVCBinding
import SDitH.Spec.BLCRecompute

/-! Exact bit-string queries used in the verifier's Hashlines/Hashaux chain.
Algorithm 12's three-field Hashlines payload is retained. No witness-correction
field is inserted to match the different four-field signer payload. -/

namespace SDitH.Spec.BLCBinding

open FieldRepresentation

def linesQuery (category : Category) {tau kappa s : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s)
    (input : BLCRecompute.LinesHashInput (width category) tau kappa s) : List Bool :=
  BAVC.byteBits 3 ++ BLCRecompute.linesPayload encoding input

def auxQuery (category : Category) {tau kappa s wit rnd : Nat}
    (encoding : ConcreteBLC.Serialization tau kappa s)
    (input : BLCCommit.AuxHashInput (width category) tau (s + (wit + rnd))) : List Bool :=
  BAVC.byteBits 2 ++ ConcreteBLC.auxPayload encoding input

def linesInput {F : Type*} {lambda tau kappa s wit rnd : Nat}
    (state : BLCRecompute.ConsistencyBoundary F lambda tau kappa s wit rnd)
    (base : Fin s → Fin tau → Fin kappa → ZMod 2) : BLCRecompute.LinesHashInput lambda tau kappa s :=
  ⟨state.auxiliaryDigest, state.auxiliary.plain, base⟩

def auxInput {F : Type*} {lambda tau kappa s wit rnd : Nat}
    (state : BLCRecompute.ConsistencyBoundary F lambda tau kappa s wit rnd) :
    BLCCommit.AuxHashInput lambda tau (s + (wit + rnd)) :=
  ⟨state.reconstruction.hcom, state.auxiliary.corrections⟩

end SDitH.Spec.BLCBinding
