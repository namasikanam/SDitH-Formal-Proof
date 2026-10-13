import SDitH.Proofs.PIOPComposition
import SDitH.Proofs.BLCArithmetic

/-! The prover polynomial's constant term vanishes for a solution. A binary
at-most-one selector's unitary check vanishes (the single set coordinate
contributes a cancelling pair, or lies beyond the shifted range); the
unitary layers vanish on binary at-most-one selectors; and with the mux
syndrome residual zero the constant term of the composed prover
polynomial is zero. -/

namespace SDitH.Proofs.ConstantTermZero

open Spec.PIOPComposition Spec.PIOPArithmetic Spec.Batching Spec.UnitaryPolynomial Spec.UniformChallenges Polynomial
open PIOPComposition
open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- A nonzero bit is one. -/
theorem zmod2_ne_zero_eq_one (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  revert h
  revert x
  decide

/-- A binary at-most-one vector's unitary check vanishes. -/
theorem unitaryCheck_binary (ξ : F) {r : Nat} (bits : Fin r → ZMod 2) (h : AtMostOne bits) :
    unitaryCheck ξ (fun k => algebraMap (ZMod 2) F (bits k)) = 0 := by
  by_cases hz : ∀ k, bits k = 0
  · simp [unitaryCheck, hz]
  · push_neg at hz
    obtain ⟨m, hm⟩ := hz
    have hone : bits m = 1 := zmod2_ne_zero_eq_one _ hm
    have hothers : ∀ k, k ≠ m → bits k = 0 := fun k hk => by
      by_contra hk0
      exact hk (h k m hk0 hm)
    have hb : ∀ k, algebraMap (ZMod 2) F (bits k) = if k = m then 1 else 0 := by
      intro k
      by_cases hk : k = m
      · subst hk
        simp [hone]
      · simp [hothers k hk, hk]
    simp only [unitaryCheck, hb, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ m, if_pos (Finset.mem_univ m)]
    by_cases hlt : m.val < r - 1
    · set m' : Fin (r - 1) := ⟨m.val, hlt⟩ with hm'
      have hcast : ∀ k : Fin (r - 1), (k.castLE (Nat.sub_le r 1) = m) ↔ k = m' := by
        intro k
        constructor
        · intro hk
          exact Fin.ext (by simpa [Fin.ext_iff] using hk)
        · intro hk
          subst hk
          exact Fin.ext rfl
      simp only [hcast]
      rw [Finset.sum_ite_eq' Finset.univ m', if_pos (Finset.mem_univ m'), Finset.sum_ite_eq' Finset.univ m',
        if_pos (Finset.mem_univ m')]
      simp only [hm']
      ring
    · have hnone : ∀ k : Fin (r - 1), k.castLE (Nat.sub_le r 1) ≠ m := by
        intro k hk
        have := congrArg Fin.val hk
        simp at this
        omega
      simp [hnone]

/-- The unitary layers vanish on binary at-most-one selectors. -/
theorem unitaryLayers_zero (ξ : F) :
    ∀ (widths : List Nat) (sel : Selectors (ZMod 2) widths) (layer : Nat),
      (∀ j : Fin widths.length, AtMostOne (selectorAt widths sel j)) →
      unitaryLayers ξ widths (mapSelectors (algebraMap (ZMod 2) F) widths sel) layer = 0
  | [], _, _, _ => rfl
  | r :: rest, sel, layer, h => by
    have hhead : AtMostOne sel.1 := by simpa [selectorAt] using h ⟨0, by simp⟩
    have htail : ∀ j : Fin rest.length, AtMostOne (selectorAt rest sel.2 j) := fun j => by
      simpa [selectorAt] using h j.succ
    simp only [unitaryLayers, mapSelectors]
    rw [unitaryCheck_binary ξ sel.1 hhead, unitaryLayers_zero ξ rest sel.2 (layer + 1) htail]
    simp

/-- The prover polynomial's constant term vanishes for a solution. -/
theorem prover_eval_zero {r k w lambda : Nat} (widths : List Nat) (hsize : leafCount widths * w = r + k) (xi : F)
    (gamma : Fin (blockCount r lambda) → F) (gammaPrime : Fin w → F) (H' : Matrix (Fin r) (Fin k) (ZMod 2))
    (y : Fin r → ZMod 2) (bits : Fin (selectorCount widths * w) → ZMod 2)
    (hres : muxSyndromeResidual widths hsize H' y bits = 0)
    (hsel : ∀ i (j : Fin widths.length), AtMostOne (selectorAt widths (formatWitness widths bits i) j))
    (witness : Fin (selectorCount widths * w) → F[X])
    (hconstants : ∀ j, (witness j).eval 0 = algebraMap (ZMod 2) F (bits j))
    (randomness : Fin (lambda * (widths.length - 1)) → F[X]) :
    (proverRun widths hsize xi gamma gammaPrime H' y witness randomness).eval 0 = 0 := by
  rw [constant_eq_batches widths hsize xi gamma gammaPrime H' y bits witness hconstants randomness, hres, map_zero]
  have hz : ∀ i, unitaryLayers xi widths (mapSelectors (algebraMap (ZMod 2) F) widths (formatWitness widths bits i)) 0 = 0 :=
    fun i => unitaryLayers_zero xi widths _ 0 (hsel i)
  simp only [linearBatch, hz, mul_zero, Finset.sum_const_zero, add_zero]

end
end SDitH.Proofs.ConstantTermZero
