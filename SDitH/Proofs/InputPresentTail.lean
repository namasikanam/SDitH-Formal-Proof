import SDitH.Proofs.HitCount
import SDitH.Proofs.CommitLinesEvents
import SDitH.Proofs.SignCompare

/-! The input-present event over the tail. The honest signing's hash input
at a prefix result's data is an injective function of the lines digest
(the payload's first component is the digest), so at a fresh lines input
the tail's run stores the input with probability at most the table's
support count over the digest count. A Boolean bind bounded off an event
by a constant is within the event's probability plus the constant. -/

namespace SDitH.Proofs.InputPresentTail

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner Spec.HashCipherTrace
open Spec.RandomOracleTrap (indicator)
open Spec.SlopeConsistencyGame (Out)
open Spec.PIOPArithmetic (selectorCount)
open SignStep SignCompare CommitDecomposition RunBind TailLinesDigest HitCount TableSupport PrefixFromHead
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A : Type*}

/-- A Boolean bind bounded off an event by a constant is within the event's
probability plus the constant. -/
theorem bind_true_le_event_add (p : PMF A) (f : A → PMF Bool) (bad : A → Bool) (K : ℝ≥0∞)
    (h : ∀ a ∈ p.support, bad a = false → (f a) true ≤ K) :
    (p.bind f) true ≤ (p.map bad) true + K := by
  have hc := bind_le_bind_add_cost p f (fun _ => PMF.pure false) (fun a => indicator (bad a) + K) true
    (fun a ha => by
      dsimp only
      cases hb : bad a with
      | true =>
        rw [RandomOracleTrap.indicator_true]
        exact (PMF.coe_le_one _ _).trans (le_add_left (le_add_right le_rfl))
      | false =>
        refine (h a ha hb).trans ?_
        rw [RandomOracleTrap.indicator_false, zero_add]
        exact le_add_left le_rfl)
  rw [PMF.bind_const] at hc
  simp only [PMF.pure_apply, Bool.true_eq_false, if_false, zero_add] at hc
  refine hc.trans (le_of_eq ?_)
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, RandomOracleTrap.map_true_eq]

end Generic

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The honest signing's hash input at a prefix result's data and a lines
digest. -/
def hashInputOf (publicKey message : List Bool) (salt : Bits lambda) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (data : PrefixData lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) (d : Digest lambda) :
    HashInput (List Bool) (List Bool) (Payload F lambda higherCount) :=
  ⟨publicKey, message, (stateOf S salt (committedOf S.signer salt witness data (d, Classical.arbitrary _))).1⟩

/-- The hash input depends on the lines answer only through its digest. -/
theorem hashInputOf_eq (publicKey message : List Bool) (salt : Bits lambda)
    (witness : Fin (selectorCount widths * w) → ZMod 2)
    (data : PrefixData lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (lines : Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    (⟨publicKey, message, (stateOf S salt (committedOf S.signer salt witness data lines)).1⟩ :
      HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) =
      hashInputOf S publicKey message salt witness data lines.1 :=
  rfl

/-- The hash input is injective in the lines digest. -/
theorem hashInputOf_injective (publicKey message : List Bool) (salt : Bits lambda)
    (witness : Fin (selectorCount widths * w) → ZMod 2)
    (data : PrefixData lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    Function.Injective (hashInputOf S publicKey message salt witness data) := by
  intro d d' h
  have := congrArg (fun x : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) => x.payload.1) h
  exact this

/-- At a fresh lines input, the tail stores the honest hash input with
probability at most the table's support count over the digest count. -/
theorem tail_present_le (publicKey message : List Bool) (salt : Bits lambda)
    (witness : Fin (selectorCount widths * w) → ZMod 2)
    (table : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda)) {n : Nat}
    (hn : Supported table n) (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (mid : Result (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda)
      (Bits lambda) (Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
        (Bits lambda) (Bits lambda) (PrefixData lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))))
    (data : PrefixData lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hstate : mid.state = .done data) (hfresh : mid.hashTable (linesInput S.signer salt witness data) = none)
    (X : Result (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda)
      (Bits lambda) (Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
        (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))) →
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    ((continueRun family 1 (commitTail S.signer salt witness) mid).map fun out =>
        decide (table ⟨publicKey, message, (preparedOf S salt (out.state, X out)).1⟩ ≠ none)) true ≤
      (n : ℝ≥0∞) * (Fintype.card (Digest lambda) : ℝ≥0∞)⁻¹ := by
  have hfun : (fun out : Result (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
      (Bits lambda) (Bits lambda) (Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
        (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))) =>
        decide (table ⟨publicKey, message, (preparedOf S salt (out.state, X out)).1⟩ ≠ none)) =
      (fun o : Option Bool => o.getD (decide (table ⟨publicKey, message, ((fun _ => false), fun _ => 0)⟩ ≠ none))) ∘
        committedOutput (fun c => decide (table ⟨publicKey, message, (stateOf S salt c).1⟩ ≠ none)) := by
    funext out
    simp only [Function.comp, committedOutput, preparedOf]
    cases out.state <;> rfl
  rw [hfun, ← PMF.map_comp, tail_output_uniform _ S.signer salt witness family mid data hstate hfresh, PMF.map_comp]
  have hfun2 : ((fun o : Option Bool => o.getD (decide (table ⟨publicKey, message, ((fun _ => false), fun _ => 0)⟩ ≠ none))) ∘
      fun lines => some (decide (table ⟨publicKey, message,
        (stateOf S salt (committedOf S.signer salt witness data lines)).1⟩ ≠ none))) =
      fun lines : Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)) =>
        decide (table (hashInputOf S publicKey message salt witness data lines.1) ≠ none) := by
    funext lines
    rfl
  rw [hfun2]
  exact uniform_hit_le table (hashInputOf S publicKey message salt witness data)
    (hashInputOf_injective S publicKey message salt witness data) hn

end
end SDitH.Proofs.InputPresentTail
