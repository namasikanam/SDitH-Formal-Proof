import SDitH.Proofs.RootTouchBound
import SDitH.Proofs.ForkOutcome

/-! Slicing the view-dependent pruning. The hidden keys of a signature are
chosen from the signature itself (through the hidden leaves) and the
family; the view pruned at them is the sum, over the possible choices, of
the views pruned at a fixed choice weighted by the indicator that the
signature makes that choice. A continuation restricted to one choice
returns nothing elsewhere, so its hit weight and recorded length carry the
indicator as a factor, which lets the touching bounds at a fixed choice
sum to the bound for the view-dependent pruning. -/

namespace SDitH.Proofs.HiddenSlice

open Spec.BAVC Spec.DomainSeparation Spec.SeedPrimitives Spec.SeedTree Spec.HashCipherProgram Spec.HashCipherTrace
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out)
open Spec.IdealCipher (Family Entry)
open Spec.RandomOracleTrap (indicator)
open OwnViewExchange NodeTouchBound RootTouchBound ForkOutcome ChargeExpect SharedPrune CommitViewExchange TreeStepFresh
open scoped Classical ENNReal

noncomputable section

variable {lambda s wit rnd : Nat} {F : Type*} [Field F] [Algebra (ZMod 2) F] {tau kappa : Nat} [NeZero tau]
  (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (witness : Fin wit → ZMod 2) (root : Bits lambda)
  {Sig : Type*}
  (post : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Committed F lambda tau kappa s wit rnd) → PMF Sig)
  (w₀ : World lambda s wit rnd)

/-- The commitment run followed by the post-processing, viewed with the
family stripped and the history pruned at keys chosen from the signature
and the family. -/
def viewPruned (K : Sig → Family (Bits lambda) (Bits lambda) → List (Bits lambda)) : PMF (Sig × World lambda s wit rnd) :=
  (runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w₀).bind fun r =>
    (post r.1).map fun q => (q, stripFamily (pruneShared (K q r.2.family) r.2))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- Means of functions agreeing on the support coincide. -/
theorem mean_congr_support {α : Type*} (p : PMF α) (φ ψ : α → ℝ≥0∞) (h : ∀ a ∈ p.support, φ a = ψ a) :
    mean p φ = mean p ψ :=
  le_antisymm (mean_le_mean _ _ _ fun a ha => (h a ha).le) (mean_le_mean _ _ _ fun a ha => (h a ha).ge)

/-- The mean of a function of the view pruned at keys chosen through a
finite selector is the sum, over the selector's values, of the means of
the views pruned at the value's keys with the view factor. -/
theorem mean_viewPruned_eq_sum {γ : Type*} [Fintype γ] (sel : Sig → γ)
    (K : γ → Family (Bits lambda) (Bits lambda) → List (Bits lambda)) (φ : Sig × World lambda s wit rnd → ℝ≥0∞) :
    mean (viewPruned S salt witness root post w₀ (fun q g => K (sel q) g)) φ =
      ∑ h : γ, mean (ownView S salt witness root post (K h w₀.family) w₀)
        (fun x => indicator (decide (sel x.1 = h)) * φ x) := by
  unfold viewPruned ownView
  simp only [mean_bind, mean_map]
  rw [sum_mean (runProgram (commitBudget tau kappa) (commitProgram S salt root witness) w₀)
    (fun h r => mean (post r.1) fun q =>
      indicator (decide (sel q = h)) * φ (q, stripFamily (pruneShared (K h w₀.family) r.2))) Finset.univ]
  refine mean_congr_support _ _ _ fun r hr => ?_
  rw [runProgram_family _ _ _ r hr,
    sum_mean (post r.1) (fun h q => indicator (decide (sel q = h)) * φ (q, stripFamily (pruneShared (K h w₀.family) r.2)))
      Finset.univ]
  refine congrArg _ (funext fun q => ?_)
  have hind : ∀ h : γ, indicator (decide (sel q = h)) * φ (q, stripFamily (pruneShared (K h w₀.family) r.2)) =
      if h = sel q then φ (q, stripFamily (pruneShared (K h w₀.family) r.2)) else 0 := by
    intro h
    by_cases hh : sel q = h
    · subst hh
      simp [indicator]
    · have hh' : h ≠ sel q := fun h' => hh h'.symm
      simp [indicator, hh, hh']
  simp only [hind, Finset.sum_ite_eq', Finset.mem_univ, if_true]

section Slice

variable {β γ : Type*} (sel : Sig → γ) (h : γ) (cont : Sig × World lambda s wit rnd → PMF β)
  (new : β → List (Entry (Bits lambda) (Bits lambda)))

/-- The continuation restricted to a selector value: elsewhere it returns
nothing. -/
def sliceCont (x : Sig × World lambda s wit rnd) : PMF (Option β) :=
  if sel x.1 = h then (cont x).map some else PMF.pure none

/-- The recorded entries of the restricted continuation. -/
def sliceNew : Option β → List (Entry (Bits lambda) (Bits lambda))
  | some y => new y
  | none => []

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- A mean under the restricted continuation of a function vanishing on
nothing carries the selector's indicator. -/
theorem mean_sliceCont (ψ : Option β → ℝ≥0∞) (hnone : ψ none = 0) (x : Sig × World lambda s wit rnd) :
    mean (sliceCont sel h cont x) ψ = indicator (decide (sel x.1 = h)) * mean (cont x) (fun y => ψ (some y)) := by
  unfold sliceCont
  by_cases hx : sel x.1 = h
  · rw [if_pos hx, mean_map]
    simp [hx, indicator]
  · rw [if_neg hx, mean_pure, hnone]
    simp [hx, indicator]

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The hit weight of a block under the restricted continuation. -/
theorem hitWeight_slice (v : Bits lambda) (x : Sig × World lambda s wit rnd) :
    hitWeight S (sliceCont sel h cont) (sliceNew new) v x =
      indicator (decide (sel x.1 = h)) * hitWeight S cont new v x := by
  unfold hitWeight
  exact mean_sliceCont sel h cont
    (fun z => indicator (decide (S.layout.key (S.layout.output v) ∈ keysOf (sliceNew new z))))
    (by simp [sliceNew, keysOf, indicator]) x

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The hit weight of a seed under the restricted continuation. -/
theorem hitWeightR_slice (r : Bits lambda) (x : Sig × World lambda s wit rnd) :
    hitWeightR S (sliceCont sel h cont) (sliceNew new) r x =
      indicator (decide (sel x.1 = h)) * hitWeightR S cont new r x := by
  unfold hitWeightR
  exact mean_sliceCont sel h cont (fun z => indicator (decide (S.layout.key r ∈ keysOf (sliceNew new z))))
    (by simp [sliceNew, keysOf, indicator]) x

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] in
/-- The expected recorded length under the restricted continuation. -/
theorem length_slice (x : Sig × World lambda s wit rnd) :
    mean (sliceCont sel h cont x) (fun z => ((sliceNew new z).length : ℝ≥0∞)) =
      indicator (decide (sel x.1 = h)) * mean (cont x) (fun y => ((new y).length : ℝ≥0∞)) :=
  mean_sliceCont sel h cont (fun z => ((sliceNew new z).length : ℝ≥0∞)) (by simp [sliceNew]) x

end Slice

end
end SDitH.Proofs.HiddenSlice
