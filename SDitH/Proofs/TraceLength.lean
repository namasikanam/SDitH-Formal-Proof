import SDitH.Proofs.InputPresentUniform

/-! The shared trace's growth along a run, and the uniform input-present
bound. A run adds at most one trace entry per unit of fuel; the mention
step is monotone in the trace length; so at a world whose trace has at
most T entries the input-present bound reads: the mention steps over the
prefix budget from T, plus the row-stored term, plus the support count
over the digest count. -/

namespace SDitH.Proofs.TraceLength

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner Spec.HashCipherTrace
open Spec.RandomOracleTrace
open Spec.PIOPArithmetic (selectorCount)
open TableSupport SharedGameInvariant InputPresentBound InputPresentUniform PrefixMentionBound SignCompare CommitSplitRun
open scoped Classical ENNReal BigOperators

noncomputable section

section Generic

variable {Input Digest Key Block State : Type*} [Fintype Digest] [Nonempty Digest]

/-- A run adds at most one trace entry per unit of fuel. -/
theorem runFixed_trace_length_le (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Spec.IdealCipher.Family Key Block) (fuel : Nat) (state : State) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) (log : List (Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support) :
    out.trace.length ≤ log.length + fuel := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    simp
  | succ fuel ih =>
    simp only [runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      simp
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      have hrec : (record table input result.1 log).length ≤ log.length + 1 := by
        unfold record
        cases table input <;> simp
      have := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers (record table input result.1 log) inner hinner
      rw [HashCipherTrace.mark_trace]
      omega
    | cipher request next =>
      have := ih _ table hashes _ log out hrest
      omega

end Generic

/-- The mention step is monotone in the trace length. -/
theorem mentionStep_mono (lambda tau : Nat) {n m : Nat} (h : n ≤ m) : mentionStep lambda tau n ≤ mentionStep lambda tau m := by
  unfold mentionStep
  exact mul_le_mul' (mul_le_mul' (Nat.cast_le.mpr h) le_rfl) le_rfl

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The input-present bound with a trace-length budget: the mention steps
from the budget, the row-stored term and the support count over the digest
count. -/
theorem inputPresent_uniform (hl : 0 < lambda) (htau : tau ≠ 0) (publicKey : List Bool)
    (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hw : WellFormed world.other) {n : Nat} (hn : Supported world.hashTable n) {T : Nat}
    (hT : world.other.trace.length ≤ T) :
    (inputPresent S publicKey witness message world) true ≤
      ∑ i ∈ Finset.range (prefixBudget tau kappa), mentionStep lambda tau (T + i) + (rowTerm S htau world) true +
        (n : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ := by
  refine (inputPresent_leN S hl htau publicKey witness message world hw hn).trans ?_
  refine add_le_add_left (add_le_add_left ((mentionTermN_le S world).trans ?_) _) _
  exact Finset.sum_le_sum fun i _ => mentionStep_mono lambda tau (by omega)

end
end SDitH.Proofs.TraceLength
