import SDitH.Spec.SlopeConsistencyGame
import SDitH.Spec.HashCipherTrace
import SDitH.Spec.SeedPairing
import SDitH.Spec.IdealCipherPairCollision

/-! The slope-consistency game in the shared hash/cipher model. Leaf
commitments are the source CommitSeed through the hidden cipher family at
the claim's salt, so the commitment-injectivity hypothesis of the
standalone game is replaced by two cipher events: a witnessed pair
collision among queried seeds, or an unqueried seed matching both halves
of a named seed's commitment. The named claim's commitment calls are
required to be in the cipher history; executing them is a later step. -/

namespace SDitH.Spec.SharedSlopeGame

open BAVC DomainSeparation BAVCChainInputs SlopeConsistency SlopeConsistencyGame SeedPrimitives SeedPairing
open IdealCipher IdealCipherPairCollision ConsistencyMatrix RandomOracleTrace
open scoped Classical
noncomputable section

structure Setting (lambda tau kappa s wit rnd : Nat) where
  p : BLCCommit.Primitives lambda tau kappa s wit rnd
  randomCount : Nat
  enough : s + (wit + rnd) ≤ 8 * randomCount
  encoding : ConcreteBLC.Serialization tau kappa s
  variant : Grinding

variable {lambda tau kappa s wit rnd : Nat} {State : Type*}

abbrev CipherFamily (lambda : Nat) := IdealCipher.Family (Bits lambda) (Bits lambda)

abbrev History (lambda : Nat) := List (IdealCipher.Entry (Bits lambda) (Bits lambda))

abbrev Res (lambda s wit rnd : Nat) (State : Type*) :=
  HashCipherTrace.Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) State

def leafCount (tau kappa : Nat) : Nat := tau * 2 ^ kappa

/-- CommitSeed through the family at a salt, as the per-leaf commitment. -/
def commitOf (variant : Grinding) (family : CipherFamily lambda) (salt : Seed lambda) : Commit lambda tau kappa :=
  fun e i seed =>
    commitSeed (leafCount tau kappa) variant (fun key input => family key input) salt seed (SeedTree.leafOffset e i)

def input0 (variant : Grinding) (salt : Seed lambda) (e : Fin tau) (i : Fin (2 ^ kappa)) : Bits lambda :=
  cipherInput variant salt (leafCount tau kappa + SeedTree.leafOffset e i) false

def seedEntry (family : CipherFamily lambda) (seed x : Bits lambda) : IdealCipher.Entry (Bits lambda) (Bits lambda) :=
  ⟨seed, x, family seed x⟩

def ChainIn' (S : Setting lambda tau kappa s wit rnd) (family : CipherFamily lambda)
    (table : List Bool → Option (Out lambda s wit rnd)) (c : Claim lambda tau kappa s wit rnd) : Prop :=
  ChainIn (commitOf S.variant family c.salt) S.encoding table c

/-- Both commitment calls of every named seed are in the cipher history. -/
def Queried (S : Setting lambda tau kappa s wit rnd) (family : CipherFamily lambda) (history : History lambda)
    (c : Claim lambda tau kappa s wit rnd) : Prop :=
  ∀ e i, seedEntry family (c.full e i) (input0 S.variant c.salt e i) ∈ history ∧
    seedEntry family (c.full e i) (companion (input0 S.variant c.salt e i)) ∈ history

/-- No other seed shares a named seed's commitment at its position. -/
def NoCollisionAt (S : Setting lambda tau kappa s wit rnd) (family : CipherFamily lambda)
    (c : Claim lambda tau kappa s wit rnd) : Prop :=
  ∀ e i seed, commitOf S.variant family c.salt e i seed = commitOf S.variant family c.salt e i (c.full e i) →
    seed = c.full e i

def slopeOf (S : Setting lambda tau kappa s wit rnd) (c : Claim lambda tau kappa s wit rnd) (e : Fin tau) :
    Fin (s + (wit + rnd)) → ZMod 2 :=
  fun col => BLCSeedFold.slope S.p c.salt c.full S.randomCount S.enough c.aux e col

def vectorOf (S : Setting lambda tau kappa s wit rnd) (family : CipherFamily lambda) (e e' : Fin tau)
    (table : List Bool → Option (Out lambda s wit rnd)) (x : List Bool) : Fin (s + (wit + rnd)) → ZMod 2 :=
  if h : ∃ c : Claim lambda tau kappa s wit rnd, ChainIn' S family table c ∧ maskInput c.auxiliary = x then
    slopeOf S (Classical.choose h) e - slopeOf S (Classical.choose h) e'
  else 0

def wins (S : Setting lambda tau kappa s wit rnd) (choose : State → Claim lambda tau kappa s wit rnd)
    (joint : CipherFamily lambda × Res lambda s wit rnd State) : Bool :=
  decide (ChainIn' S joint.1 joint.2.hashTable (choose joint.2.state) ∧
    Queried S joint.1 joint.2.cipherHistory (choose joint.2.state) ∧
    ∃ pair, joint.2.hashTable (maskInput (choose joint.2.state).auxiliary) = some pair ∧
      ∃ e e', slopeOf S (choose joint.2.state) e ≠ slopeOf S (choose joint.2.state) e' ∧
        ∀ a, masked pair.2 (slopeOf S (choose joint.2.state) e) a = masked pair.2 (slopeOf S (choose joint.2.state) e') a)

def trapAny (S : Setting lambda tau kappa s wit rnd) (joint : CipherFamily lambda × Res lambda s wit rnd State) : Bool :=
  decide (∃ e e' : Fin tau, traceBad (ProductOracle.tableMaskTrap (vectorOf S joint.1 e e')) joint.2.trace = true)

def witnessed (joint : CipherFamily lambda × Res lambda s wit rnd State) : Bool :=
  decide (Witnessed id companion joint.1 joint.2.cipherHistory)

/-- A seed unqueried at both paired inputs matching both recorded halves of
a named seed's commitment. The named seed's entries are in the history, so
the targets are recorded values. -/
def unseenMatch (S : Setting lambda tau kappa s wit rnd) (choose : State → Claim lambda tau kappa s wit rnd)
    (joint : CipherFamily lambda × Res lambda s wit rnd State) : Bool :=
  decide (∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (seed out0 out1 : Bits lambda),
    seed ≠ (choose joint.2.state).full e i ∧
    Unseen joint.2.cipherHistory seed (input0 S.variant (choose joint.2.state).salt e i) ∧
    Unseen joint.2.cipherHistory seed (companion (input0 S.variant (choose joint.2.state).salt e i)) ∧
    (⟨(choose joint.2.state).full e i, input0 S.variant (choose joint.2.state).salt e i, out0⟩ :
      IdealCipher.Entry (Bits lambda) (Bits lambda)) ∈ joint.2.cipherHistory ∧
    (⟨(choose joint.2.state).full e i, companion (input0 S.variant (choose joint.2.state).salt e i), out1⟩ :
      IdealCipher.Entry (Bits lambda) (Bits lambda)) ∈ joint.2.cipherHistory ∧
    joint.1 seed (input0 S.variant (choose joint.2.state).salt e i) = out0 ∧
    joint.1 seed (companion (input0 S.variant (choose joint.2.state).salt e i)) = out1)

end
end SDitH.Spec.SharedSlopeGame
