import SDitH.Spec.BLCSeedFold

/-! The suffix witness/randomness values and the consistency columns for the
affine share matrix of `BLCSeedFold`. `rowPsi` is the psi contribution of one
execution's Gray row. `CandidateConsistency` is one explicit binary reading of
the ill-typed Algorithm-12 line 21, stated as a hypothesis shape for the
two-challenge theorems; it is not asserted to be the source's meaning and
the literal line remains an unresolved boundary. -/

namespace SDitH.Spec.BLCSeedLines

open BLCSeedFold DomainSeparation

variable {lambda tau kappa s wit rnd : Nat}

/-- psi of the single row e of the Gray challenge matrix. -/
noncomputable def rowPsi {F : Type*} [CommRing F] [Algebra (ZMod 2) F] (xi : F)
    (hidden : Fin tau → Fin (2 ^ kappa)) (e : Fin tau) : F :=
  ∑ j : Fin kappa, algebraMap (ZMod 2) F (GrayCode.grayFieldRow (hidden e) j) * xi ^ (e.val * kappa + j.val)

/-- The share matrix at the hidden indices, as the fold produces it. -/
def shareMatrix (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : BLCCommit.Auxiliary tau s wit rnd)
    (hidden : Fin tau → Fin (2 ^ kappa)) : Fin (s + (wit + rnd)) → Fin tau → Fin kappa → ZMod 2 :=
  fun c e j => affine p salt full randomCount enough aux e (hidden e) c j

def interceptMatrix (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) : Fin (s + (wit + rnd)) → Fin tau → Fin kappa → ZMod 2 :=
  fun c e j => intercept p salt full randomCount enough e c j

/-- [I | M] applied to the slope of execution e. -/
def maskedSlope (p : BLCCommit.Primitives lambda tau kappa s wit rnd) (salt : Bits lambda)
    (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (aux : BLCCommit.Auxiliary tau s wit rnd)
    (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (e : Fin tau) (a : Fin s) : ZMod 2 :=
  ∑ c, Batching.systematicLeft M a c * slope p salt full randomCount enough aux e c

/-- A candidate binary reading of line 21: the consistency columns equal the
plain check times the hidden Gray row plus a base matrix. Supplying this
shape is a review choice; it is not derived from the printed scalar line. -/
def CandidateConsistency (M : Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)) (plain : Fin s → ZMod 2)
    (base : Fin s → Fin tau → Fin kappa → ZMod 2) (Q : Fin (s + (wit + rnd)) → Fin tau → Fin kappa → ZMod 2)
    (hidden : Fin tau → Fin (2 ^ kappa)) : Prop :=
  ∀ a e j, BLC.consistencyColumns M Q a e j = plain a * GrayCode.grayFieldRow (hidden e) j + base a e j

end SDitH.Spec.BLCSeedLines
