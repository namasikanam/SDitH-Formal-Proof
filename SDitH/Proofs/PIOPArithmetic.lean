import SDitH.Spec.PIOPArithmetic
import Mathlib.Tactic

namespace SDitH.Proofs.PIOPArithmetic

open Polynomial Spec.PIOPArithmetic
open scoped BigOperators

variable {R S : Type*}

theorem selectorCount_eq_sum (widths : List Nat) : selectorCount widths = widths.sum := by
  induction widths with
  | nil => rfl
  | cons r rest ih => simp [selectorCount, ih]

theorem map_parseSelectors (f : R → S) (widths : List Nat)
    (flat : Fin (selectorCount widths) → R) :
    mapSelectors f widths (parseSelectors widths flat) =
      parseSelectors widths (fun k => f (flat k)) := by
  induction widths with
  | nil => rfl
  | cons r rest ih => simp [mapSelectors, parseSelectors, ih]

theorem map_formatWitness (f : R → S) {w : Nat} (widths : List Nat)
    (flat : Fin (selectorCount widths * w) → R) :
    (fun i => mapSelectors f widths (formatWitness widths flat i)) =
      formatWitness widths (fun k => f (flat k)) := by
  funext i
  exact map_parseSelectors f widths _

variable [CommRing R] [CommRing S]

theorem map_mux (f : R →+* S) {r : Nat} (bits : Fin r → R) (values : Fin (r+1) → R) :
    f (mux bits values) = mux (fun k => f (bits k)) (fun k => f (values k)) := by
  simp [mux, map_sum]

theorem map_unitaryCheck (f : R →+* S) (ξ : R) {r : Nat} (bits : Fin r → R) :
    f (unitaryCheck ξ bits) = unitaryCheck (f ξ) (fun k => f (bits k)) := by
  simp [unitaryCheck, map_sum]

theorem map_formatMask (f : R →+* S) {d lambda : Nat} (ξ z : R)
    (randomness : Fin (d - 1) → Fin lambda → R) :
    f (formatMask ξ z randomness) = formatMask (f ξ) (f z) (fun i j => f (randomness i j)) := by
  simp [formatMask, map_sum]

theorem map_muxTree (f : R →+* S) (widths : List Nat) (selectors : Selectors R widths)
    (leaves : Fin (leafCount widths) → R) :
    f (muxTree widths selectors leaves) =
      muxTree widths (mapSelectors f widths selectors) (fun j => f (leaves j)) := by
  induction widths with
  | nil => rfl
  | cons r rest ih =>
    simp only [muxTree, mapSelectors]
    rw [ih]
    simp only [map_mux]

theorem map_unitaryLayers (f : R →+* S) (ξ : R) (widths : List Nat)
    (selectors : Selectors R widths) (layer : Nat) :
    f (unitaryLayers ξ widths selectors layer) =
      unitaryLayers (f ξ) widths (mapSelectors f widths selectors) layer := by
  induction widths generalizing layer with
  | nil => simp [unitaryLayers]
  | cons r rest ih =>
    simp [unitaryLayers, mapSelectors, map_unitaryCheck, ih]

theorem map_runArithmetic (f : R →+* S) {w : Nat} (widths : List Nat)
    (ξ z mask syndrome : R) (gamma : Fin w → R) (selectors : Fin w → Selectors R widths)
    (columns : Fin w → Fin (leafCount widths) → R) :
    f (runArithmetic widths ξ z mask syndrome gamma selectors columns) =
      runArithmetic widths (f ξ) (f z) (f mask) (f syndrome) (fun i => f (gamma i))
        (fun i => mapSelectors f widths (selectors i)) (fun i j => f (columns i j)) := by
  simp [runArithmetic, map_sum, map_muxTree, map_unitaryLayers]

/-- The full shared PIOP arithmetic commutes with polynomial evaluation. It
assumes no semantic correctness contract about mux trees, unitary checks, or
formatting; all three are expanded implementations checked above.

This does not prove `Pα(0)=0` for the source's witness encoding, nor link BLC,
hashes, or serialization. Those remaining obligations cannot be inferred from
this arithmetic identity. -/
theorem verifier_evaluates_prover {w lambda : Nat} (widths : List Nat) (ξ Δ syndrome : R)
    (gamma : Fin w → R) (selectors : Fin w → Selectors R[X] widths)
    (randomness : Fin (widths.length - 1) → Fin lambda → R[X])
    (columns : Fin w → Fin (leafCount widths) → R) :
    (proverArithmetic widths ξ syndrome gamma selectors randomness columns).eval Δ =
      verifierArithmetic widths ξ Δ syndrome gamma
        (fun i => mapSelectors (Polynomial.eval Δ) widths (selectors i))
        (fun i j => (randomness i j).eval Δ) columns := by
  unfold proverArithmetic verifierArithmetic
  change (Polynomial.evalRingHom Δ) _ = _
  rw [map_runArithmetic]
  simp [map_formatMask]

/-- The same correspondence includes the actual flat-array parsing loops. -/
theorem verifier_evaluates_prover_flat {w lambda : Nat} (widths : List Nat) (ξ Δ syndrome : R)
    (gamma : Fin w → R) (witness : Fin (selectorCount widths * w) → R[X])
    (randomness : Fin (lambda * (widths.length - 1)) → R[X])
    (columns : Fin w → Fin (leafCount widths) → R) :
    (proverArithmeticFlat widths ξ syndrome gamma witness randomness columns).eval Δ =
      verifierArithmeticFlat widths ξ Δ syndrome gamma
        (fun k => (witness k).eval Δ) (fun k => (randomness k).eval Δ) columns := by
  unfold proverArithmeticFlat verifierArithmeticFlat
  rw [verifier_evaluates_prover, map_formatWitness]
  rfl

end SDitH.Proofs.PIOPArithmetic
