import SDitH.Spec.PIOPArithmetic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

namespace SDitH.Proofs.PIOPDegree

open Polynomial Spec.PIOPArithmetic
open scoped BigOperators

variable {F : Type*} [Field F]

theorem parseSelectors_linear (widths : List Nat) (flat : Fin (selectorCount widths) → F[X])
    (h : ∀ i, (flat i).natDegree ≤ 1) :
    LinearSelectors widths (parseSelectors widths flat) := by
  induction widths with
  | nil => trivial
  | cons r rest ih =>
    exact ⟨fun i => h _, ih _ (fun i => h _)⟩

theorem formatWitness_linear {w : Nat} (widths : List Nat)
    (flat : Fin (selectorCount widths * w) → F[X])
    (h : ∀ i, (flat i).natDegree ≤ 1) (i : Fin w) :
    LinearSelectors widths (formatWitness widths flat i) :=
  parseSelectors_linear widths _ (fun j => h (blockIndex i j))

private theorem sum_bound {I : Type*} [Fintype I] (p : I → F[X]) (d : Nat)
    (h : ∀ i, (p i).natDegree ≤ d) : (∑ i, p i).natDegree ≤ d :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => h i)

private theorem constant_pow_mul_bound (ξ : F) (k d : Nat) (p : F[X])
    (h : p.natDegree ≤ d) : ((C ξ) ^ k * p).natDegree ≤ d := by
  have hc : ((C ξ : F[X]) ^ k).natDegree ≤ 0 := by
    simp
  simpa using Polynomial.natDegree_mul_le_of_le hc h

theorem unitaryCheck_degree {r : Nat} (ξ : F) (bits : Fin r → F[X])
    (hb : ∀ k, (bits k).natDegree ≤ 1) :
    (unitaryCheck (C ξ) bits).natDegree ≤ 2 := by
  have h₁ := sum_bound (fun k => (C ξ) ^ k.val * bits k) 1
    (fun k => constant_pow_mul_bound ξ k.val 1 (bits k) (hb k))
  have h₂ := sum_bound
    (fun k : Fin (r - 1) => (C ξ) ^ (r * k.val) * bits (k.castLE (Nat.sub_le r 1))) 1
    (fun k => constant_pow_mul_bound ξ _ 1 _ (hb _))
  have h₃ := sum_bound
    (fun k : Fin (r - 1) => (C ξ) ^ ((r + 1) * k.val) * bits (k.castLE (Nat.sub_le r 1))) 1
    (fun k => constant_pow_mul_bound ξ _ 1 _ (hb _))
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (Polynomial.natDegree_mul_le_of_le h₁ h₂) (h₃.trans (by omega)))

theorem mux_degree {r : Nat} (bits : Fin r → F[X]) (values : Fin (r + 1) → F[X])
    (a : Nat) (hb : ∀ k, (bits k).natDegree ≤ 1)
    (hv : ∀ k, (values k).natDegree ≤ a) :
    (mux bits values).natDegree ≤ a + 1 := by
  unfold mux
  apply Polynomial.natDegree_add_le_of_degree_le ((hv 0).trans (by omega))
  apply sum_bound
  intro k
  have hsub := (Polynomial.natDegree_sub_le _ _).trans (max_le (hv k.succ) (hv 0))
  simpa [Nat.add_comm] using Polynomial.natDegree_mul_le_of_le (hb k) hsub

theorem muxTree_degree (widths : List Nat) (selectors : Selectors F[X] widths)
    (leaves : Fin (leafCount widths) → F[X]) (a : Nat)
    (hs : LinearSelectors widths selectors) (hl : ∀ j, (leaves j).natDegree ≤ a) :
    (muxTree widths selectors leaves).natDegree ≤ a + widths.length := by
  induction widths generalizing a with
  | nil => simpa [muxTree] using hl ⟨0, by decide⟩
  | cons r rest ih =>
    have hnext := ih selectors.2
      (fun row => mux selectors.1 (fun col => leaves (blockIndex row col))) (a + 1)
      hs.2 (fun row => mux_degree _ _ a hs.1 (fun col => hl (blockIndex row col)))
    simpa [muxTree, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

theorem unitaryLayers_degree (ξ : F) (widths : List Nat) (selectors : Selectors F[X] widths)
    (layer : Nat) (hs : LinearSelectors widths selectors) :
    (unitaryLayers (C ξ) widths selectors layer).natDegree ≤ 2 := by
  induction widths generalizing layer with
  | nil => simp [unitaryLayers]
  | cons r rest ih =>
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact constant_pow_mul_bound ξ _ 2 _ (unitaryCheck_degree ξ _ hs.1)
    · exact ih _ (layer + 1) hs.2

theorem formatMask_degree {d lambda : Nat} (hd : 2 ≤ d) (ξ : F)
    (randomness : Fin (d - 1) → Fin lambda → F[X])
    (hr : ∀ i j, (randomness i j).natDegree ≤ 1) :
    (formatMask (C ξ) X randomness).natDegree ≤ d - 1 := by
  unfold formatMask
  apply sum_bound
  intro i
  have hinner := sum_bound (fun j => (C ξ) ^ j.val * randomness i j) 1
    (fun j => constant_pow_mul_bound ξ _ 1 _ (hr i j))
  have hx : ((X : F[X]) ^ (d - 2 - i.val)).natDegree ≤ d - 2 - i.val := by simp
  exact (Polynomial.natDegree_mul_le_of_le hinner hx).trans (by omega)

/-- The genuine degree bound of the computed output polynomial. Its proof uses
the implemented routines. It does not assume the output degree as a contract. -/
theorem proverArithmetic_degree {w lambda : Nat} (widths : List Nat) (hd : 2 ≤ widths.length)
    (ξ syndrome : F) (gamma : Fin w → F) (selectors : Fin w → Selectors F[X] widths)
    (randomness : Fin (widths.length - 1) → Fin lambda → F[X])
    (columns : Fin w → Fin (leafCount widths) → F)
    (hs : ∀ i, LinearSelectors widths (selectors i))
    (hr : ∀ i j, (randomness i j).natDegree ≤ 1) :
    (proverArithmetic widths ξ syndrome gamma selectors randomness columns).natDegree ≤
      widths.length := by
  unfold proverArithmetic runArithmetic
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · have hm := formatMask_degree hd ξ randomness hr
      have hx : (X : F[X]).natDegree ≤ 1 := by simp
      exact (Polynomial.natDegree_mul_le_of_le hm hx).trans (by omega)
    · simp
  · apply sum_bound
    intro i
    apply Polynomial.natDegree_add_le_of_degree_le
    · simpa using muxTree_degree widths (selectors i) (fun j => C (columns i j)) 0
        (hs i) (fun j => by simp)
    · have hu := (unitaryLayers_degree ξ widths (selectors i) 0 (hs i)).trans hd
      have hc : (C (gamma i)).natDegree ≤ 0 := by simp
      simpa using Polynomial.natDegree_mul_le_of_le hc hu

/-- Output degree bound in the original flat-array interface. -/
theorem proverArithmeticFlat_degree {w lambda : Nat} (widths : List Nat)
    (hd : 2 ≤ widths.length) (ξ syndrome : F) (gamma : Fin w → F)
    (witness : Fin (selectorCount widths * w) → F[X])
    (randomness : Fin (lambda * (widths.length - 1)) → F[X])
    (columns : Fin w → Fin (leafCount widths) → F)
    (hw : ∀ i, (witness i).natDegree ≤ 1)
    (hr : ∀ i, (randomness i).natDegree ≤ 1) :
    (proverArithmeticFlat widths ξ syndrome gamma witness randomness columns).natDegree ≤
      widths.length :=
  proverArithmetic_degree widths hd ξ syndrome gamma _ _ columns
    (formatWitness_linear widths witness hw) (fun i j => hr (blockIndex i j))

end SDitH.Proofs.PIOPDegree
