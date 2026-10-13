import SDitH.Proofs.ThreeHashRun

/-! The trace shape of three consecutive fresh hash queries. Iterating the
fresh hash step, every run result of a program that makes three hash
queries at fresh inputs and finishes has the three answers stored, the
three entries recorded newest first on the trace, and the finished state
at the three answers. This is the shape of the end of the commitment's
prefix (outer, auxiliary and mask queries). -/

namespace SDitH.Proofs.ThreeHashShape

open Spec.HashCipherTrace Spec.HashCipherProgram Spec.RandomOracleTrace ThreeHashRun
open scoped Classical

noncomputable section

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

/-- The run of a finished program with no fuel is its result. -/
theorem runFixed_zero_support (family : Spec.IdealCipher.Family Key Block) (value : A) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (runFixed procedure family 0 (.done value) table hashes ciphers log).support) :
    out = ⟨.done value, table, hashes, ciphers, false, log⟩ := by
  simp only [runFixed, PMF.mem_support_pure_iff] at hout
  exact hout

/-- Three fresh hash queries: stored answers, recorded entries, finished
state. -/
theorem three_hash_support (family : Spec.IdealCipher.Family Key Block) (outerIn : Input) (auxIn : Digest → Input)
    (maskIn : Digest → Digest → Input) (k : Digest → Digest → Digest → A) (t0 : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (h0 : t0 outerIn = none) (h1 : ∀ o, Function.update t0 outerIn (some o) (auxIn o) = none)
    (h2 : ∀ o a, Function.update (Function.update t0 outerIn (some o)) (auxIn o) (some a) (maskIn o a) = none)
    (out : Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (runFixed procedure family 3
      (.hash outerIn fun o => .hash (auxIn o) fun a => .hash (maskIn o a) fun m => .done (k o a m))
      t0 hashes ciphers log).support) :
    ∃ o a m : Digest,
      let t1 := Function.update t0 outerIn (some o)
      let t2 := Function.update t1 (auxIn o) (some a)
      out.state = .done (k o a m) ∧
      out.hashTable = Function.update t2 (maskIn o a) (some m) ∧
      out.trace = ⟨t2, maskIn o a, m⟩ :: ⟨t1, auxIn o, a⟩ :: ⟨t0, outerIn, o⟩ :: log := by
  obtain ⟨o, out1, hout1, heq1⟩ := runFixed_hash_fresh_support family 2 outerIn _ t0 hashes ciphers log h0 out hout
  obtain ⟨a, out2, hout2, heq2⟩ := runFixed_hash_fresh_support family 1 (auxIn o) _ _ _ ciphers _ (h1 o) out1 hout1
  obtain ⟨m, out3, hout3, heq3⟩ := runFixed_hash_fresh_support family 0 (maskIn o a) _ _ _ ciphers _ (h2 o a) out2 hout2
  have h3 := runFixed_zero_support family (k o a m) _ _ ciphers _ out3 hout3
  refine ⟨o, a, m, ?_, ?_, ?_⟩
  · rw [heq1, (mark_fields _ _).1, heq2, (mark_fields _ _).1, heq3, (mark_fields _ _).1, h3]
  · rw [heq1, (mark_fields _ _).2.1, heq2, (mark_fields _ _).2.1, heq3, (mark_fields _ _).2.1, h3]
  · rw [heq1, (mark_fields _ _).2.2.2.2, heq2, (mark_fields _ _).2.2.2.2, heq3, (mark_fields _ _).2.2.2.2, h3]

end
end SDitH.Proofs.ThreeHashShape
