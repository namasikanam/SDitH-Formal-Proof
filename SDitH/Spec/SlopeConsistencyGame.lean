import SDitH.Spec.SlopeConsistency

/-! The standalone slope-consistency game on the product-valued oracle. An
adaptive procedure queries hash strings and mask inputs; its final state
names a claim. It wins when the claim is chained in the final table, the
mask for its auxiliary digest is stored, and two executions' slopes differ
yet have equal images under that mask. The trap vector for a pair of
executions is defined from the claim chained in the table before the mask
query, through classical choice; uniqueness is proved separately. The
setting's primitives, commitment function and serializer are supplied
inputs; their injectivity hypotheses are explicit in the bound. -/

namespace SDitH.Spec.SlopeConsistencyGame

open BAVC DomainSeparation BAVCChainInputs SlopeConsistency RandomOracleTrace ConsistencyMatrix
open scoped Classical
noncomputable section

structure Setting (lambda tau kappa s wit rnd : Nat) where
  p : BLCCommit.Primitives lambda tau kappa s wit rnd
  randomCount : Nat
  enough : s + (wit + rnd) ≤ 8 * randomCount
  commit : Commit lambda tau kappa
  encoding : ConcreteBLC.Serialization tau kappa s

abbrev Mask (s wit rnd : Nat) := Matrix (Fin s) (Fin (wit + rnd)) (ZMod 2)

abbrev Out (lambda s wit rnd : Nat) := Digest lambda × Mask s wit rnd

variable {lambda tau kappa s wit rnd : Nat} {State : Type*}

def slopeOf (S : Setting lambda tau kappa s wit rnd) (c : Claim lambda tau kappa s wit rnd) (e : Fin tau) :
    Fin (s + (wit + rnd)) → ZMod 2 :=
  fun col => BLCSeedFold.slope S.p c.salt c.full S.randomCount S.enough c.aux e col

/-- The trap vector for executions e, e': the slope difference of a claim
chained in the given table whose mask input is the query. -/
def vectorOf (S : Setting lambda tau kappa s wit rnd) (e e' : Fin tau)
    (table : List Bool → Option (Out lambda s wit rnd)) (x : List Bool) : Fin (s + (wit + rnd)) → ZMod 2 :=
  if h : ∃ c : Claim lambda tau kappa s wit rnd, ChainIn S.commit S.encoding table c ∧ maskInput c.auxiliary = x then
    slopeOf S (Classical.choose h) e - slopeOf S (Classical.choose h) e'
  else 0

def wins (S : Setting lambda tau kappa s wit rnd) (choose : State → Claim lambda tau kappa s wit rnd)
    (out : Result (List Bool) (Out lambda s wit rnd) State) : Bool :=
  decide (ChainIn S.commit S.encoding out.table (choose out.state) ∧
    ∃ pair, out.table (maskInput (choose out.state).auxiliary) = some pair ∧
      ∃ e e', slopeOf S (choose out.state) e ≠ slopeOf S (choose out.state) e' ∧
        ∀ a, masked pair.2 (slopeOf S (choose out.state) e) a = masked pair.2 (slopeOf S (choose out.state) e') a)

/-- Some pair of executions raised the table-dependent mask trap. -/
def trapAny (S : Setting lambda tau kappa s wit rnd) (out : Result (List Bool) (Out lambda s wit rnd) State) : Bool :=
  decide (∃ e e' : Fin tau, traceBad (ProductOracle.tableMaskTrap (vectorOf S e e')) out.trace = true)

end
end SDitH.Spec.SlopeConsistencyGame
