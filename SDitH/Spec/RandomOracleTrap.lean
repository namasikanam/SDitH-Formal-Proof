import SDitH.Spec.RandomOracleCollision
import SDitH.Spec.ConsistencyMatrix

/-! A trap predicate on query/answer pairs of the adaptive lazy oracle. The
predicate is a fixed function of the query input and the fresh answer, so an
adversary cannot choose the input after seeing the answer. The kernel trap
asks whether a fixed vector-valued function of the input is annihilated by
the mask returned for that input. This is the oracle-ordering shape needed
for the consistency mask; it is not a claim about concrete XOF outputs. -/

namespace SDitH.Spec.RandomOracleTrap

open scoped Classical ENNReal

variable {Input Output : Type*}

/-- Some recorded query/answer pair satisfies the trap predicate. -/
def historyBad (bad : Input → Output → Bool) (history : List (Input × Output)) : Bool :=
  history.any fun old => bad old.1 old.2

noncomputable def indicator (b : Bool) : ℝ≥0∞ := if b then 1 else 0

/-- The mask trap for a fixed vector-valued function of the query input. -/
noncomputable def kernelTrap {K : Type*} [CommRing K] {s payload : Nat} (vector : Input → Fin (s + payload) → K)
    (input : Input) (M : Matrix (Fin s) (Fin payload) K) : Bool :=
  decide (vector input ≠ 0 ∧ ∀ a, ConsistencyMatrix.masked M (vector input) a = 0)

end SDitH.Spec.RandomOracleTrap
