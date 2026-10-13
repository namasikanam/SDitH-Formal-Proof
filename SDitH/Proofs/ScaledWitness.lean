import SDitH.Spec.ScaledWitness
import SDitH.Proofs.WitnessExpansion
import SDitH.Proofs.SDReduction
import SDitH.Proofs.PIOPDegree
import SDitH.Proofs.PIOPArithmetic
import SDitH.Proofs.MuxLinearity

namespace SDitH.Proofs.ScaledWitness

open Spec.ScaledWitness Spec.PIOPArithmetic Spec.SDReduction
open scoped Classical BigOperators

theorem vector_coordinate {F : Type*} [Field F] {w m : Nat} (wit : Witness F w m)
    (i : Fin w) (j : Fin m) :
    vector wit (finProdFinEquiv (i, j)) = (wit.amplitudes i).val * Spec.elementary (wit.positions i) j := by
  simp [vector]

theorem vector_regular {F : Type*} [Field F] {w m : Nat} (wit : Witness F w m) :
    regularFlat (vector wit) := by
  intro i
  exact ⟨wit.positions i, (wit.amplitudes i).val, (wit.amplitudes i).property,
    funext (fun j => vector_coordinate wit i j)⟩

theorem vector_weight {F : Type*} [Field F] {w m : Nat} (wit : Witness F w m) :
    Spec.hammingWeight (vector wit) = w :=
  SDReduction.regularFlat_weight (vector wit) (vector_regular wit)

/-- The syndrome is the sum of the selected matrix columns, each multiplied
by its chunk's nonzero value, exactly as described for the larger-field variant. -/
theorem syndrome_columns {F : Type*} [Field F] {w m r : Nat} (wit : Witness F w m)
    (H : Matrix (Fin r) (Fin (w * m)) F) (row : Fin r) :
    H.mulVec (vector wit) row =
      ∑ i, (wit.amplitudes i).val * H row (finProdFinEquiv (i, wit.positions i)) := by
  change (∑ j, H row j * vector wit j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv (m := w) (n := m)) (fun j => H row j * vector wit j)]
  rw [Fintype.sum_prod_type]
  simp_rw [vector_coordinate]
  apply Finset.sum_congr rfl
  intro i _
  simp [Spec.elementary, mul_comm]

/-- The positions and their nonzero values are determined by the actual
solution vector, not merely by a serialized witness contract. -/
theorem vector_injective {F : Type*} [Field F] {w m : Nat} :
    Function.Injective (vector (F := F) (w := w) (m := m)) := by
  intro a b h
  have hp : a.positions = b.positions := by
    funext i
    by_contra hi
    have hv := congrFun h (finProdFinEquiv (i, a.positions i))
    rw [vector_coordinate, vector_coordinate] at hv
    simp [Spec.elementary, hi] at hv
    exact (a.amplitudes i).property hv
  have ha : a.amplitudes = b.amplitudes := by
    funext i
    apply Subtype.ext
    have hv := congrFun h (finProdFinEquiv (i, a.positions i))
    rw [vector_coordinate, vector_coordinate, hp] at hv
    simpa [Spec.elementary] using hv
  exact Witness.ext hp ha

theorem regular_iff_encoded {F : Type*} [Field F] {w m : Nat} (x : Fin (w * m) → F) :
    regularFlat x ↔ ∃ wit : Witness F w m, vector wit = x := by
  constructor
  · intro h
    choose p a ha hx using h
    refine ⟨⟨p, fun i => ⟨a i, ha i⟩⟩, ?_⟩
    funext j
    obtain ⟨ij, rfl⟩ := finProdFinEquiv.surjective j
    rw [vector_coordinate]
    exact (congrFun (hx ij.1) ij.2).symm
  · rintro ⟨wit, rfl⟩
    exact vector_regular wit

def witnessProductEquiv {F : Type*} [Zero F] (w m : Nat) :
    Witness F w m ≃ (Fin w → Fin m × {a : F // a ≠ 0}) where
  toFun wit i := (wit.positions i, wit.amplitudes i)
  invFun f := ⟨fun i => (f i).1, fun i => (f i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def regularVectorEquiv {F : Type*} [Field F] (w m : Nat) :
    Witness F w m ≃ {x : Fin (w * m) → F // regularFlat x} :=
  Equiv.ofBijective (fun wit => ⟨vector wit, vector_regular wit⟩) (by
    constructor
    · intro a b h
      exact vector_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨wit, hwit⟩ := (regular_iff_encoded x.val).mp x.property
      exact ⟨wit, Subtype.ext hwit⟩)

/-- The number of regular vectors over a finite field includes one independent
nonzero value per chunk. This is not only the count of their supports. -/
theorem regular_vector_count {F : Type*} [Field F] [Fintype F] (w m : Nat) :
    Nat.card {x : Fin (w * m) → F // regularFlat x} =
      (m * (Fintype.card F - 1)) ^ w := by
  rw [← Nat.card_congr (regularVectorEquiv (F := F) w m),
    Nat.card_congr (witnessProductEquiv (F := F) w m)]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

theorem positionBits_length {F : Type*} [Zero F] {w m d : Nat}
    (width : Fin d → Nat) (wit : Witness F w m) :
    (positionBits width wit).length = w * ∑ j, width j :=
  WitnessExpansion.expansion_witness_length width wit.positions

theorem positionBits_and_values_injective {F : Type*} [Zero F] {w m d : Nat}
    (width : Fin d → Nat) (hm : m ≤ Spec.WitnessExpansion.radixSize width)
    (a b : Witness F w m) (hp : positionBits width a = positionBits width b)
    (ha : a.amplitudes = b.amplitudes) : a = b := by
  exact Witness.ext (WitnessExpansion.expansion_witness_injective width hm _ _ hp) ha

/-- Scaling the reconstructed binary tensor gives the stated nonzero value
at precisely its represented position, under the given binary-field algebra. -/
theorem scaled_completed_tensor {F : Type*} [Field F] [Algebra (ZMod 2) F]
    {d : Nat} (width : Fin d → Nat) (position : Nat)
    (hp : position < Spec.WitnessExpansion.radixSize width) (amplitude : F)
    (coordinate : (j : Fin d) → Fin (width j + 1)) :
    amplitude * algebraMap (ZMod 2) F
      (Spec.tensor (fun j => Spec.completeSelector
        (Spec.WitnessExpansion.selector width position j)) coordinate) =
      if Spec.WitnessExpansion.joinDigits width coordinate = position then amplitude else 0 := by
  rw [WitnessExpansion.completed_tensor_coordinate width position hp]
  split_ifs <;> simp

theorem scaledMux_evaluation {F : Type*} [Field F]
    (amplitude : Polynomial F) (widths : List Nat)
    (selectors : Selectors (Polynomial F) widths)
    (leaves : Fin (leafCount widths) → Polynomial F) (delta : F) :
    (scaledMux amplitude widths selectors leaves).eval delta =
      scaledMux (amplitude.eval delta) widths
        (mapSelectors (fun p => p.eval delta) widths selectors) (fun j => (leaves j).eval delta) := by
  simpa only [scaledMux, Polynomial.eval_mul] using congrArg
    (fun x => amplitude.eval delta * x)
    (PIOPArithmetic.map_muxTree (Polynomial.evalRingHom delta) widths selectors leaves)

theorem batch_scaledMux {K F : Type*} [CommRing K] [CommRing F] [Algebra K F]
    {r : Nat} (L : (Fin r → K) →ₗ[K] F) (amplitude : K) (widths : List Nat)
    (selectors : Selectors K widths) (leaves : Fin (leafCount widths) → Fin r → K) :
    L (fun row => scaledMux amplitude widths selectors (fun j => leaves j row)) =
      scaledMux (algebraMap K F amplitude) widths
        (mapSelectors (algebraMap K F) widths selectors) (fun j => L (leaves j)) := by
  change L (amplitude • (fun row => muxTree widths selectors (fun j => leaves j row))) = _
  rw [map_smul, MuxLinearity.map_muxTree]
  exact Algebra.smul_def _ _

/-- One line for the amplitude adds at most one degree to the selector tree. -/
theorem scaledMux_degree {F : Type*} [Field F] (amplitude : Polynomial F)
    (widths : List Nat) (selectors : Selectors (Polynomial F) widths)
    (leaves : Fin (leafCount widths) → F)
    (ha : amplitude.natDegree ≤ 1) (hs : LinearSelectors widths selectors) :
    (scaledMux amplitude widths selectors (fun j => Polynomial.C (leaves j))).natDegree ≤
      widths.length + 1 := by
  have ht := PIOPDegree.muxTree_degree widths selectors
    (fun j => Polynomial.C (leaves j)) 0 hs (fun j => by simp)
  simpa [scaledMux, Nat.add_comm] using Polynomial.natDegree_mul_le_of_le ha ht

end SDitH.Proofs.ScaledWitness
