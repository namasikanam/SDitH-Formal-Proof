import SDitH.Spec.BLCArithmetic
import SDitH.Spec.FieldRepresentation

/-! The explicit binary and Gray interpretations of Algorithm-11/12 indices.
The source defines bin_kappa in most-significant-first order, and uses Gray
rows in folding, but feeds unannotated indices to psi in the headers. Both
maps below remain named alternatives. Neither is installed as a silent source
correction. The same concrete Table-2 generator is used for both merges.
-/

namespace SDitH.Spec.ChallengeEncoding

open FieldRepresentation

def zeroIndex (kappa : Nat) : Fin (2 ^ kappa) := ⟨0, pow_pos (by decide) _⟩

def binaryFieldRow {kappa : Nat} (i : Fin (2 ^ kappa)) : Fin kappa → ZMod 2 :=
  fun j => if GrayCode.binaryRow i j then 1 else 0

def grayIndex {kappa : Nat} (i : Fin (2 ^ kappa)) : Fin (2 ^ kappa) :=
  ⟨GrayCode.grayWord i.val,
    Nat.xor_lt_two_pow i.isLt (lt_of_le_of_lt (Nat.div_le_self _ _) i.isLt)⟩

def grayIndices {tau kappa : Nat} (hidden : Fin tau → Fin (2 ^ kappa)) :
    Fin tau → Fin (2 ^ kappa) := fun e => grayIndex (hidden e)

noncomputable def binaryMerge (category : Category) {tau kappa : Nat}
    (hidden : Fin tau → Fin (2 ^ kappa)) : QuotientRing category :=
  BLC.psi (generator category) (BLC.challengeRow binaryFieldRow hidden)

noncomputable def grayMerge (category : Category) {tau kappa : Nat}
    (hidden : Fin tau → Fin (2 ^ kappa)) : QuotientRing category :=
  BLC.psi (generator category) (BLC.challengeRow GrayCode.grayFieldRow hidden)

end SDitH.Spec.ChallengeEncoding
