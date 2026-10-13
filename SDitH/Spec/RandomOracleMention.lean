import SDitH.Spec.RandomOracleTrace

/-! Trap predicates that may depend on the whole fresh-query trace preceding
a query, with a per-query bound depending on how many fresh entries precede
it. The mention instance asks whether a fresh answer equals a value that an
earlier query input already mentioned, for an explicit mention map. This is
the guessing event charged when a hash preimage chain is completed only
after a value derived from it was used. -/

namespace SDitH.Spec.RandomOracleMention

open RandomOracleTrace
open scoped Classical

variable {Input Output : Type*}

/-- Some fresh entry satisfies the predicate at the trace preceding it. The
trace is newest first, so the preceding trace of an entry is its tail. -/
def prefixBad (bad : List (Entry Input Output) → Input → Output → Bool) :
    List (Entry Input Output) → Bool
  | [] => false
  | entry :: rest => bad rest entry.input entry.answer || prefixBad bad rest

/-- A fresh answer equal to a value mentioned by an earlier fresh query input. -/
noncomputable def mentionBad (mentions : Input → Finset Output) (trace : List (Entry Input Output))
    (_input : Input) (answer : Output) : Bool :=
  trace.any fun entry => decide (answer ∈ mentions entry.input)

end SDitH.Spec.RandomOracleMention
