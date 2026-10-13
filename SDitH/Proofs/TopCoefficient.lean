import SDitH.Proofs.PIOPDegree
import SDitH.Proofs.PIOPMaskCoeff

/-! The top coefficient of the mux tree and of the prover polynomial depends
only on the slopes of the selector lines. The coefficient of degree a+1 of a
mux of degree-one selectors over values of degree at most a is the slope
mux of the values' top coefficients, so by induction the top coefficient
of the mux tree is the slope tree of the leaves; the unitary layers have
degree at most two and do not reach the top for at least three layers, and
the mask's top coefficient is the packed slope of layer zero. Hence the
last hashed coefficient is independent of the lines' constants, in
particular of the witness. -/

namespace SDitH.Proofs.TopCoefficient

open Polynomial Spec.PIOPArithmetic Spec.PIOPComposition Spec.Batching
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F]

/-- The slope mux: the mux without its base value. -/
def topMux {r : Nat} (slopes : Fin r → F) (tops : Fin (r + 1) → F) : F :=
  ∑ k, slopes k * (tops k.succ - tops 0)

/-- The slope tree, mirroring the mux tree with slope muxes. -/
def muxTreeTop : (widths : List Nat) → Selectors F widths → (Fin (leafCount widths) → F) → F
  | [], _, tops => tops ⟨0, by decide⟩
  | _ :: rest, slopes, tops =>
      muxTreeTop rest slopes.2 (fun row => topMux slopes.1 (fun col => tops (blockIndex row col)))

/-- The slopes of linear selectors. -/
def slopesOf : (widths : List Nat) → Selectors F[X] widths → Selectors F widths :=
  mapSelectors (fun p => p.coeff 1)

/-- The degree-(a+1) coefficient of a mux of degree-one selectors over values of
degree at most a is the slope mux of the values' degree-a coefficients. -/
theorem mux_top {r : Nat} (bits : Fin r → F[X]) (values : Fin (r + 1) → F[X]) (a : Nat)
    (hb : ∀ k, (bits k).natDegree ≤ 1) (hv : ∀ k, (values k).natDegree ≤ a) :
    (mux bits values).coeff (a + 1) = topMux (fun k => (bits k).coeff 1) (fun k => (values k).coeff a) := by
  unfold mux topMux
  rw [coeff_add, finset_sum_coeff, coeff_eq_zero_of_natDegree_lt ((hv 0).trans_lt (Nat.lt_succ_self a)), zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsub : (values k.succ - values 0).natDegree ≤ a := (natDegree_sub_le _ _).trans (max_le (hv _) (hv 0))
  rw [show a + 1 = 1 + a by omega, coeff_mul_add_eq_of_natDegree_le (hb k) hsub, coeff_sub]

/-- The degree-(a + depth) coefficient of the mux tree over leaves of degree at
most a is the slope tree of the leaves' degree-a coefficients. -/
theorem muxTree_top (widths : List Nat) (selectors : Selectors F[X] widths) (leaves : Fin (leafCount widths) → F[X])
    (a : Nat) (hs : LinearSelectors widths selectors) (hl : ∀ j, (leaves j).natDegree ≤ a) :
    (muxTree widths selectors leaves).coeff (a + widths.length) =
      muxTreeTop widths (slopesOf widths selectors) (fun j => (leaves j).coeff a) := by
  induction widths generalizing a with
  | nil => simp [muxTree, muxTreeTop]
  | cons r rest ih =>
    have hnext := ih selectors.2 (fun row => mux selectors.1 (fun col => leaves (blockIndex row col))) (a + 1) hs.2
      (fun row => PIOPDegree.mux_degree _ _ a hs.1 (fun col => hl (blockIndex row col)))
    simp only [muxTree, muxTreeTop, slopesOf, mapSelectors, List.length_cons]
    rw [show a + (rest.length + 1) = a + 1 + rest.length by omega, hnext]
    congr 1
    funext row
    exact mux_top selectors.1 _ a hs.1 (fun col => hl (blockIndex row col))

/-- With at least three layers the unitary layers do not reach the top. -/
theorem unitaryLayers_top (xi : F) (widths : List Nat) (selectors : Selectors F[X] widths) (hd : 3 ≤ widths.length)
    (hs : LinearSelectors widths selectors) :
    (unitaryLayers (C xi) widths selectors 0).coeff widths.length = 0 :=
  coeff_eq_zero_of_natDegree_lt ((PIOPDegree.unitaryLayers_degree xi widths selectors 0 hs).trans_lt (by omega))

/-- The top coefficient of the prover arithmetic: the slope trees of the
chunks plus the mask's top coefficient; the constants of the lines (in
particular the witness) do not appear. -/
theorem proverArithmetic_top {w lambda : Nat} (widths : List Nat) (hd : 3 ≤ widths.length) (xi syndrome : F)
    (gamma : Fin w → F) (selectors : Fin w → Selectors F[X] widths)
    (randomness : Fin (widths.length - 1) → Fin lambda → F[X]) (columns : Fin w → Fin (leafCount widths) → F)
    (hs : ∀ i, LinearSelectors widths (selectors i)) :
    (proverArithmetic widths xi syndrome gamma selectors randomness columns).coeff widths.length =
      (formatMask (C xi) X randomness).coeff (widths.length - 1) +
        ∑ i, muxTreeTop widths (slopesOf widths (selectors i)) (columns i) := by
  unfold proverArithmetic runArithmetic
  rw [coeff_add, coeff_sub, finset_sum_coeff]
  have hmask : (formatMask (C xi) X randomness * X).coeff widths.length =
      (formatMask (C xi) X randomness).coeff (widths.length - 1) := by
    have h := coeff_mul_X (formatMask (C xi) X randomness) (widths.length - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ widths.length)] at h
  have hsyn : (C syndrome : F[X]).coeff widths.length = 0 := by
    rw [coeff_C, if_neg (by omega)]
  rw [hmask, hsyn, sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [coeff_add, coeff_C_mul, unitaryLayers_top xi widths (selectors i) hd (hs i), mul_zero, add_zero]
  have htree := muxTree_top widths (selectors i) (fun j => C (columns i j)) 0 (hs i) (fun j => by simp)
  rw [Nat.zero_add] at htree
  rw [htree]
  congr 1
  funext j
  simp

end
end SDitH.Proofs.TopCoefficient
