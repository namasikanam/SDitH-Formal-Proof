import SDitH.Spec.BAVCChainInputs
import SDitH.Spec.BLCSeedLines

/-! Claims behind a mask query: seeds, row digests, root, auxiliary digest
and transmitted auxiliary data, with leaf commitments computed by a supplied
commitment function and corrections encoded by a supplied serializer. A
claim is chained in a table when its row, outer and auxiliary strings are
stored with the claimed digests. The digest-collision event on the
instrumented log records a fresh digest equal to an earlier fresh digest.
No injectivity of the commitment or serializer is asserted here; those are
explicit hypotheses of the uniqueness theorem. -/

namespace SDitH.Spec.SlopeConsistency

open BAVC DomainSeparation BAVCChainInputs RandomOracleTrace
open scoped Classical

structure Claim (lambda tau kappa s wit rnd : Nat) where
  salt : Seed lambda
  full : Fin tau → Fin (2 ^ kappa) → Bits lambda
  rowHashes : Fin tau → Digest lambda
  root : Digest lambda
  auxiliary : Digest lambda
  aux : BLCCommit.Auxiliary tau s wit rnd

variable {lambda tau kappa s wit rnd : Nat} {M : Type*}

/-- A commitment function per leaf position: in the source, CommitSeed with
the salt and leaf index, whose binding is bounded separately. -/
abbrev Commit (lambda tau kappa : Nat) := Fin tau → Fin (2 ^ kappa) → Bits lambda → Digest lambda

def rows (commit : Commit lambda tau kappa) (c : Claim lambda tau kappa s wit rnd) (e : Fin tau) :
    Fin (2 ^ kappa) → Digest lambda :=
  fun i => commit e i (c.full e i)

def tail (encoding : ConcreteBLC.Serialization tau kappa s) (c : Claim lambda tau kappa s wit rnd) : List Bool :=
  BLCHashChain.sourceTail encoding c.aux.corrections

/-- The claim's three kinds of chain strings are stored with its digests. -/
def ChainIn (commit : Commit lambda tau kappa) (encoding : ConcreteBLC.Serialization tau kappa s)
    (table : List Bool → Option (Digest lambda × M)) (c : Claim lambda tau kappa s wit rnd) : Prop :=
  (∀ e, ∃ pair, table (rowString (rows commit c e)) = some pair ∧ pair.1 = c.rowHashes e) ∧
    (∃ pair, table (outerString c.salt c.rowHashes) = some pair ∧ pair.1 = c.root) ∧
    ∃ pair, table (auxString c.root (tail encoding c)) = some pair ∧ pair.1 = c.auxiliary

def DigestCollisionFree (table : List Bool → Option (Digest lambda × M)) : Prop :=
  ∀ x y px py, table x = some px → table y = some py → px.1 = py.1 → x = y

/-- A fresh digest component equal to an earlier fresh digest component. -/
noncomputable def digestCollision (log : List (Entry (List Bool) (Digest lambda × M))) (_input : List Bool)
    (answer : Digest lambda × M) : Bool :=
  log.any fun entry => decide (entry.answer.1 = answer.1)

end SDitH.Spec.SlopeConsistency
