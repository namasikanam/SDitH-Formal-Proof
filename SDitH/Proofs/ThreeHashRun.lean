import SDitH.Proofs.FreshHashUniform
import SDitH.Spec.HashCipherTrace
import SDitH.Spec.HashCipherProgram

/-! The traced run of three consecutive fresh hash queries. For a program
that makes three hash queries and finishes, with each query's input absent
from the table it is asked on, every run result has the three answers
recorded newest first on the trace, the three answers stored in the table
and the finished state at the three answers. This is the trace shape of
the end of the commitment's prefix (outer, auxiliary and mask queries),
used to locate a stored lines input among the older entries. -/

namespace SDitH.Proofs.ThreeHashRun

open Spec.HashCipherTrace Spec.HashCipherProgram Spec.RandomOracle Spec.RandomOracleTrace
open scoped Classical

noncomputable section

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

/-- A single fresh hash step: the run's results are the continuation's runs at
a stored fresh answer with the entry recorded. -/
theorem runFixed_hash_fresh_support (family : Spec.IdealCipher.Family Key Block) (n : Nat) (input : Input)
    (next : Digest → Program Input Digest Key Block A) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Entry Input Digest)) (hfresh : table input = none)
    (out : Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (runFixed procedure family (n + 1) (.hash input next) table hashes ciphers log).support) :
    ∃ answer : Digest, ∃ out' ∈ (runFixed procedure family n (next answer) (Function.update table input (some answer))
        ((input, answer) :: hashes) ciphers (⟨table, input, answer⟩ :: log)).support,
      out = mark (Spec.RandomOracleCollision.freshHit table hashes input answer) out' := by
  have hstep : (procedure : Spec.HashCipher.Procedure Input Digest Key Block
      (Program Input Digest Key Block A)).step (.hash input next) = PMF.pure (.hash input next) := rfl
  simp only [runFixed, hstep, PMF.pure_bind] at hout
  obtain ⟨result, hres, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨out', hout', heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  have htable := FreshHashUniform.query_fresh_table table input hfresh result hres
  have hrecord : record table input result.1 log = ⟨table, input, result.1⟩ :: log := by
    simp [record, hfresh]
  refine ⟨result.1, out', ?_, heq.symm⟩
  rw [← htable, ← hrecord]
  exact hout'

omit [Fintype Digest] [Nonempty Digest] in
/-- The marked result keeps every field but the collision flag. -/
theorem mark_fields (hit : Bool) (out : Result Input Digest Key Block A) :
    (mark hit out).state = out.state ∧ (mark hit out).hashTable = out.hashTable ∧
      (mark hit out).hashHistory = out.hashHistory ∧ (mark hit out).cipherHistory = out.cipherHistory ∧
      (mark hit out).trace = out.trace := by
  simp [mark]

end
end SDitH.Proofs.ThreeHashRun
