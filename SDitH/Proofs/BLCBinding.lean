import SDitH.Spec.BLCBinding
import SDitH.Proofs.BLCRecompute
import SDitH.Proofs.BAVCBindingReconstruction

namespace SDitH.Proofs.BLCBinding

open Spec.DomainSeparation Spec.FieldRepresentation Spec.BLCBinding Spec.BAVCBinding

/-- A fixed-length header is recoverable independently of the unspecified
encoding and lengths of the following fields. -/
theorem fixed_header_eq {n : Nat} (domainBits : List Bool) (left right : Bits n)
    (leftTail rightTail : List Bool)
    (h : domainBits ++ (List.ofFn left ++ leftTail) = domainBits ++ (List.ofFn right ++ rightTail)) :
    left = right := by
  have he := List.append_cancel_left h
  exact List.ofFn_injective (List.append_inj he (by simp)).1

theorem lines_query_recovers_aux (category : Category) {tau kappa s : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s)
    (left right : Spec.BLCRecompute.LinesHashInput (width category) tau kappa s)
    (h : linesQuery category encoding left = linesQuery category encoding right) :
    left.auxiliary = right.auxiliary := by
  apply fixed_header_eq (Spec.BAVC.byteBits 3) left.auxiliary right.auxiliary
    (encoding.vector left.plain ++ encoding.base left.base)
    (encoding.vector right.plain ++ encoding.base right.base)
  simpa only [linesQuery, Spec.BLCRecompute.linesPayload, List.append_assoc] using h

theorem aux_query_recovers_commitment (category : Category) {tau kappa s wit rnd : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s)
    (left right : Spec.BLCCommit.AuxHashInput (width category) tau (s + (wit + rnd)))
    (h : auxQuery category encoding left = auxQuery category encoding right) :
    left.commitment = right.commitment := by
  exact fixed_header_eq (Spec.BAVC.byteBits 2) left.commitment right.commitment _ _ h

/-- These exact digest and reconstruction equations follow from reaching the
actual line-21 boundary. They are not assumed correctness of recomputation. -/
theorem prepare_commitment_link {F : Type} [Field F] [DecidableEq F]
    {lambda tau kappa B wit rnd wpow : Nat}
    (p : Spec.BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
    (salt : Bits lambda) (aux : Spec.BLCCommit.Auxiliary tau (lambda + B) wit rnd)
    (decomposition : Spec.BLCRetry.Counter × Spec.BAVC.Opening lambda tau)
    (expand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (bindings : Spec.BLCRecompute.Bindings lambda tau kappa ((lambda + B) + (wit + rnd)))
    (randomCount consistencyCount : Nat)
    (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount)
    (state : Spec.BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd)
    (h : Spec.BLCRecompute.prepareWithBindings p salt aux decomposition expand encode Topen bindings
      randomCount consistencyCount hrandom hconsistency = .ok state) :
    state.auxiliaryDigest = p.hashAux (auxInput state) ∧
      Spec.BAVC.reconstructWithNodes
        (Spec.SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash)
        salt (expand decomposition.1).hidden decomposition.2 Topen bindings.nodes = .ok state.reconstruction := by
  obtain ⟨_, _, reconstruction, folded, shares, hr, _, _, rfl⟩ :=
    (BLCRecompute.prepare_ok_iff p salt aux decomposition expand encode Topen bindings
      randomCount consistencyCount hrandom hconsistency state).mp h
  exact ⟨rfl, hr⟩

/-- Equal recomputed line digests imply equal BAVC roots, or a collision on one
of the actual Hashlines/Hashaux query pairs. No serializer injectivity is assumed:
only the leading fixed-width digest is recovered. The two auxiliary equations
are supplied by prepare_commitment_link for successful actual prefixes. -/
theorem same_lines_root_or_collision {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (category : Category) (variant : Grinding) {tau kappa s wit rnd : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa s) (xi : F)
    (left right : Spec.BLCRecompute.ConsistencyBoundary F (width category) tau kappa s wit rnd)
    (leftBase rightBase : Fin s → Fin tau → Fin kappa → ZMod 2)
    (hl : left.auxiliaryDigest = (Spec.ConcreteBLC.primitives category variant encoding).hashAux (auxInput left))
    (hr : right.auxiliaryDigest = (Spec.ConcreteBLC.primitives category variant encoding).hashAux (auxInput right))
    (h : (Spec.BLCRecompute.suffix xi (Spec.BLCRecompute.concreteHashLines category encoding) left leftBase).lines =
      (Spec.BLCRecompute.suffix xi (Spec.BLCRecompute.concreteHashLines category encoding) right rightBase).lines) :
    left.reconstruction.hcom = right.reconstruction.hcom ∨
      HashCollision (Spec.SHAKE.hash category)
        (linesQuery category encoding (linesInput left leftBase), linesQuery category encoding (linesInput right rightBase)) ∨
      HashCollision (Spec.SHAKE.hash category)
        (auxQuery category encoding (auxInput left), auxQuery category encoding (auxInput right)) := by
  by_cases hlines : linesQuery category encoding (linesInput left leftBase) =
      linesQuery category encoding (linesInput right rightBase)
  · have haux : left.auxiliaryDigest = right.auxiliaryDigest :=
      lines_query_recovers_aux category encoding _ _ hlines
    have hhash : Spec.SHAKE.hash category (auxQuery category encoding (auxInput left)) =
        Spec.SHAKE.hash category (auxQuery category encoding (auxInput right)) := hl.symm.trans (haux.trans hr)
    by_cases hqueries : auxQuery category encoding (auxInput left) = auxQuery category encoding (auxInput right)
    · exact Or.inl (aux_query_recovers_commitment category encoding _ _ hqueries)
    · exact Or.inr (Or.inr ⟨hqueries, hhash⟩)
  · exact Or.inr (Or.inl ⟨hlines, h⟩)

/-- The two hash-chain equations are discharged from the two actual prepared
prefixes. The supplied base matrices remain the documented line-21 boundary;
this statement does not silently implement that ill-typed source operation. -/
theorem prepared_same_lines_root_or_collision {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    (category : Category) (variant : Grinding) {tau kappa B wit rnd wpow : Nat}
    (encoding : Spec.ConcreteBLC.Serialization tau kappa (width category + B)) (xi : F)
    (leftSalt rightSalt : Bits (width category))
    (leftAux rightAux : Spec.BLCCommit.Auxiliary tau (width category + B) wit rnd)
    (leftDecomposition rightDecomposition : Spec.BLCRetry.Counter × Spec.BAVC.Opening (width category) tau)
    (leftExpand rightExpand : Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
    (leftBindings rightBindings : Spec.BLCRecompute.Bindings (width category) tau kappa
      ((width category + B) + (wit + rnd)))
    (randomCount consistencyCount : Nat)
    (hrandom : (width category + B) + (wit + rnd) ≤ 8 * randomCount)
    (hconsistency : wit + rnd ≤ 8 * consistencyCount)
    (left right : Spec.BLCRecompute.ConsistencyBoundary F (width category) tau kappa (width category + B) wit rnd)
    (leftBase rightBase : Fin (width category + B) → Fin tau → Fin kappa → ZMod 2)
    (hl : Spec.BLCRecompute.prepareWithBindings (Spec.ConcreteBLC.primitives category variant encoding)
      leftSalt leftAux leftDecomposition leftExpand encode Topen leftBindings
      randomCount consistencyCount hrandom hconsistency = .ok left)
    (hr : Spec.BLCRecompute.prepareWithBindings (Spec.ConcreteBLC.primitives category variant encoding)
      rightSalt rightAux rightDecomposition rightExpand encode Topen rightBindings
      randomCount consistencyCount hrandom hconsistency = .ok right)
    (h : (Spec.BLCRecompute.suffix xi (Spec.BLCRecompute.concreteHashLines category encoding) left leftBase).lines =
      (Spec.BLCRecompute.suffix xi (Spec.BLCRecompute.concreteHashLines category encoding) right rightBase).lines) :
    left.reconstruction.hcom = right.reconstruction.hcom ∨
      HashCollision (Spec.SHAKE.hash category)
        (linesQuery category encoding (linesInput left leftBase), linesQuery category encoding (linesInput right rightBase)) ∨
      HashCollision (Spec.SHAKE.hash category)
        (auxQuery category encoding (auxInput left), auxQuery category encoding (auxInput right)) := by
  apply same_lines_root_or_collision category variant encoding xi left right leftBase rightBase
  · exact (prepare_commitment_link _ leftSalt leftAux leftDecomposition leftExpand encode Topen
      leftBindings randomCount consistencyCount hrandom hconsistency left hl).1
  · exact (prepare_commitment_link _ rightSalt rightAux rightDecomposition rightExpand encode Topen
      rightBindings randomCount consistencyCount hrandom hconsistency right hr).1
  · exact h

end SDitH.Proofs.BLCBinding
