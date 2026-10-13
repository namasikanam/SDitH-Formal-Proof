import SDitH.Proofs.StaleNotGood
import SDitH.Proofs.RowStoredPosterior

/-! The staleness term's bound. The staleness event of the run before the
last call is at most the tree's not-good event, whose probability under
the posterior family is at most the indicator of the root's key being
among the starting keys plus the steps times the step bound; averaging
over the uniform root, the indicator's mean is the number of roots whose
key is among the starting keys over the number of seeds. So the staleness
term is at most the root term plus the steps times the step bound. -/

namespace SDitH.Proofs.StaleTermBound

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.HashCipherTrace
open Spec.RandomOracleTrap
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Matches)
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.AbstractSignature
open Spec.PIOPArithmetic (selectorCount)
open RowStoredPosterior RowStoredAfter RowStoredCount TreeStepFresh TreeGoodInduction StaleNotGood HeadCommitSplit
open CipherResample RunHybrid InputPresentTail
open scoped Classical ENNReal

noncomputable section

section Uniform

variable {A : Type*} [Fintype A] [Nonempty A]

/-- A uniform draw satisfies a predicate with probability the predicate's
count over the type's size. -/
theorem uniform_event_eq (P : A → Prop) [DecidablePred P] :
    ((PMF.uniformOfFintype A).map fun a => decide (P a)) true =
      (Fintype.card {a // P a} : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
  rw [RandomOracleTrap.map_true_eq, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, mul_comm]
  congr 1
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : P a <;> simp [h, indicator]

end Uniform

variable {lambda : Nat}

/-- The seeds whose key lies in a finite set number at most the key map's
fiber bound times the set's size. -/
theorem count_key_root (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (cKey : Nat)
    (hkey : ∀ κ, Fintype.card {r : Bits lambda // layout.key r = κ} ≤ cKey) (K : Finset (Bits lambda))
    (inst : Fintype {r : Bits lambda // layout.key r ∈ K}) :
    @Fintype.card {r : Bits lambda // layout.key r ∈ K} inst ≤ cKey * K.card := by
  rw [card_instance_eq inst inferInstance, Fintype.card_subtype]
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun r => layout.key r) (t := K)
    (fun r hr => (Finset.mem_filter.mp hr).2) cKey (fun κ _ => ?_)
  calc _ ≤ (Finset.univ.filter fun r : Bits lambda => layout.key r = κ).card :=
        Finset.card_le_card fun r hr => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          exact hr.2
    _ = Fintype.card {r : Bits lambda // layout.key r = κ} := (Fintype.card_subtype _).symm
    _ ≤ cKey := hkey κ

/-- A uniform root's key lies in a finite set with probability at most the
fiber bound times the set's size over the number of seeds. -/
theorem root_key_le (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (cKey : Nat)
    (hkey : ∀ κ, Fintype.card {r : Bits lambda // layout.key r = κ} ≤ cKey) (K : Finset (Bits lambda)) :
    ((PMF.uniformOfFintype (Bits lambda)).map fun root => decide (layout.key root ∈ K)) true ≤
      ((cKey * K.card : Nat) : ℝ≥0∞) * (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ := by
  rw [uniform_event_eq]
  exact mul_le_mul' ((Nat.cast_le (α := ℝ≥0∞)).mpr (count_key_root layout cKey hkey K _)) le_rfl

variable {tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The staleness term is at most the root term plus the steps times the
step bound. -/
theorem staleTerm_le (htau : tau ≠ 0)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (hpos : ∃ family : Family (Bits lambda) (Bits lambda), Matches family world.other.cipherHistory)
    (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hkey : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (h₀ : Nat) (hH : world.other.cipherHistory.length ≤ h₀) (q : Nat) (hq : h₀ + 2 * (tau * 2 ^ kappa - 1) ≤ q) :
    staleTerm S htau world ≤
      ((cKey * (keysOf world.other.cipherHistory).card : Nat) : ℝ≥0∞) * (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ +
        ((tau * 2 ^ kappa - 1 : Nat) : ℝ≥0∞) * (2 * (((c * (keysOf world.other.cipherHistory).card : Nat) : ℝ≥0∞) /
          ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞))) := by
  set B : ℝ≥0∞ := 2 * (((c * (keysOf world.other.cipherHistory).card : Nat) : ℝ≥0∞) /
    ((Fintype.card (Bits lambda) - q : Nat) : ℝ≥0∞)) with hB
  set R : ℝ≥0∞ := ((cKey * (keysOf world.other.cipherHistory).card : Nat) : ℝ≥0∞) *
    (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ with hR
  unfold staleTerm
  have hpoint : ∀ salt root : Bits lambda,
      ((posterior world.other.cipherHistory).bind fun family =>
        (runFixed procedure family (beforeBudget tau kappa) (headBefore htau S.signer salt root) world.other.hashTable
          world.other.hashHistory world.other.cipherHistory world.other.trace).map (staleOf htau S.signer salt)) true ≤
      indicator (decide (S.signer.layout.key root ∈ keysOf world.other.cipherHistory)) +
        ((tau * 2 ^ kappa - 1 : Nat) : ℝ≥0∞) * B := by
    intro salt root
    refine (bind_true_le_bind_true _ _ _ fun family _ =>
      stale_le_notGood htau S.signer salt root hin hl hL family _ _ _ _).trans ?_
    have hsteps : tau * 2 ^ kappa - 1 < 2 * (tau * 2 ^ kappa) := by
      have := Nat.two_pow_pos kappa
      have : 0 < tau * 2 ^ kappa := Nat.mul_pos (Nat.pos_of_ne_zero htau) this
      omega
    exact tree_good_le S.signer.layout S.signer.variant salt root hin hl (tau * 2 ^ kappa) hL c hfiber _ hpos q _ _ _
      (tau * 2 ^ kappa - 1) hsteps (by omega)
  have hroot : ∀ salt : Bits lambda,
      ((PMF.uniformOfFintype (Bits lambda)).bind fun root =>
        (posterior world.other.cipherHistory).bind fun family =>
          (runFixed procedure family (beforeBudget tau kappa) (headBefore htau S.signer salt root) world.other.hashTable
            world.other.hashHistory world.other.cipherHistory world.other.trace).map (staleOf htau S.signer salt)) true ≤
      R + ((tau * 2 ^ kappa - 1 : Nat) : ℝ≥0∞) * B := by
    intro salt
    refine (bind_true_le_event_add _ _ (fun root => decide (S.signer.layout.key root ∈ keysOf world.other.cipherHistory))
      (((tau * 2 ^ kappa - 1 : Nat) : ℝ≥0∞) * B) fun root _ hbad => ?_).trans (add_le_add_left (root_key_le _ cKey hkey _) _)
    have hbad' : decide (S.signer.layout.key root ∈ keysOf world.other.cipherHistory) = false := hbad
    have := hpoint salt root
    rwa [hbad', RandomOracleTrap.indicator_false, zero_add] at this
  refine (bind_le_bind_add_const' _ _ (fun _ => PMF.pure false) (R + ((tau * 2 ^ kappa - 1 : Nat) : ℝ≥0∞) * B) true
    fun salt _ => ?_).trans ?_
  · exact (hroot salt).trans (by simp)
  · simp [PMF.bind_const]

end
end SDitH.Proofs.StaleTermBound
