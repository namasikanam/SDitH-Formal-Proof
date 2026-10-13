import SDitH.Spec.ProductOracle

/-! Ordering of the instrumented log and dependency chains of queries.
The log is newest first. `Ordered` says a newer entry's earlier table
extends an older entry's earlier table and already stores the older value.
A dependency chain lists queries sink-first: each input mentions the digest
expected of the next (older) link. These are bookkeeping definitions for
relating a mask query to the hash chain present when it was answered. -/

namespace SDitH.Spec.OracleChain

open RandomOracleTrace

variable {Input Output : Type*}

def Ordered (log : List (Entry Input Output)) : Prop :=
  ∀ (i j : Nat) (hi : i < log.length) (hj : j < log.length), i < j →
    Extends (log[j]).before (log[i]).before ∧
      (log[i]).before (log[j]).input = some (log[j]).answer

def Fresh (log : List (Entry Input Output)) : Prop :=
  ∀ entry ∈ log, entry.before entry.input = none

/-- Consecutive links: the later (newer) link's input mentions the digest
expected of the earlier link. The list is sink-first. -/
def Linked {D : Type*} (mentions : Input → Finset D) : List (Input × D) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => q.2 ∈ mentions p.1 ∧ Linked mentions (q :: rest)

/-- The newest link's input mentions the digest expected of the head link. -/
def LinkedTo {D : Type*} (mentions : Input → Finset D) (sink : Input) : List (Input × D) → Prop
  | [] => True
  | p :: _ => p.2 ∈ mentions sink

/-- Every link's digest component is stored at its input. -/
def Stored {D M : Type*} (table : Input → Option (D × M)) (links : List (Input × D)) : Prop :=
  ∀ p ∈ links, ∃ pair, table p.1 = some pair ∧ pair.1 = p.2

/-- All link inputs are present in a table. -/
def Present {D M : Type*} (table : Input → Option (D × M)) (links : List (Input × D)) : Prop :=
  ∀ p ∈ links, (table p.1).isSome

end SDitH.Spec.OracleChain
