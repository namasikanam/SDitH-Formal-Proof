import SDitH.Proofs.WitnessExpansion
import SDitH.Proofs.PIOPArithmetic

/-! A coherent small arithmetic instance connects Algorithm 1's actual witness
to the detailed PIOP's flat parser and constant term. It is not a submitted
parameter row or a full signature execution. Both radices are three, the chunk
length is nine, and the sampled position is zero. Thus the Table-3 dimension
discrepancy is not responsible for this counterexample. -/

namespace SDitH.Proofs.WitnessPIOPDiscrepancy

open Spec Spec.WitnessExpansion Spec.PIOPArithmetic Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

def widths : Fin 2 → Nat := fun _ => 2
def positions : Fin 1 → Fin 9 := fun _ => 0

def flatWitness : Fin (selectorCount [2, 2] * 1) → F := ![1, 0, 1, 0]

/-- The first systematic parity-check column is one; every other column is
zero. The syndrome of the sampled elementary solution is therefore one. -/
def columns : Fin 1 → Fin (leafCount [2, 2]) → F :=
  fun _ j => if j.val = 0 then 1 else 0

def smallInstance : SDInstance F 9 8 :=
  { H := fun _ j => if j.val = 0 then 1 else 0
    y := fun _ => 1 }

theorem dimensions_match : radixSize widths = 9 := by decide

theorem expanded_witness_is_flat :
    (expandAfterSampling (F := F) widths positions).witness = List.ofFn (flatWitness (F := F)) := by
  simp [expandAfterSampling, widths, positions, witnessLoop, flatWitness, List.ofFn_succ]

theorem expanded_solution_first (j : Fin 9) :
    (expandAfterSampling (F := F) widths positions).solution (finProdFinEquiv (0, j)) =
      if j.val = 0 then 1 else 0 := by
  rw [WitnessExpansion.expansion_solution_coordinate]
  change elementary (0 : Fin 9) j = _
  have he : j = (0 : Fin 9) ↔ j.val = 0 := Fin.ext_iff
  simp only [elementary, he]

/-- The generated solution satisfies the one-row syndrome equation. -/
theorem generated_solution_syndrome :
    (∑ j : Fin (leafCount [2, 2]), columns (F := F) 0 j *
      (expandAfterSampling (F := F) widths positions).solution (finProdFinEquiv (0, j))) = 1 := by
  change (∑ j : Fin 9, columns (F := F) 0 j *
    (expandAfterSampling (F := F) widths positions).solution (finProdFinEquiv (0, j))) = 1
  simp only [expanded_solution_first, columns]
  have he : (∑ j : Fin 9,
      (if j.val = 0 then (1 : F) else 0) * (if j.val = 0 then 1 else 0)) =
      ∑ j : Fin 9, if j = 0 then (1 : F) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val = 0 <;> simp [hj, Fin.ext_iff]
  rw [he]
  exact Finset.sum_ite_eq_of_mem' Finset.univ (0 : Fin 9) (fun _ => (1 : F)) (Finset.mem_univ 0)

theorem generated_solution_valid :
    SDSolution (smallInstance (F := F)) 1
      (expandAfterSampling (F := F) widths positions).solution := by
  refine ⟨?_, WitnessExpansion.expansion_weight widths positions⟩
  funext row
  change (∑ j : Fin 9, (if j.val = 0 then (1 : F) else 0) *
    (expandAfterSampling (F := F) widths positions).solution j) = 1
  have hi (j : Fin 9) : finProdFinEquiv ((0 : Fin 1), j) = j := by
    apply Fin.ext
    simp [finProdFinEquiv]
  simpa only [columns, hi] using generated_solution_syndrome (F := F)

/-- The actual two-layer flat parser and printed mux arithmetic yield -1 on
that valid solution, for every unitary batching challenge and field generator. -/
theorem detailed_verifier_at_zero (xi : F) (gamma : Fin 1 → F) :
    verifierArithmeticFlat (lambda := 128) [2, 2] xi 0 1 gamma flatWitness (fun _ => 0) columns =
      -1 := by
  simp only [verifierArithmeticFlat, verifierArithmetic, runArithmetic, mul_zero, zero_sub]
  norm_num [formatWitness, parseSelectors, flatWitness, selectorCount, blockIndex,
    muxTree, mux, unitaryLayers, unitaryCheck, columns, Fin.sum_univ_succ]

/-- Consequently the detailed prover polynomial does not have the zero constant
term claimed for honest witnesses. This evaluates the actual arithmetic, not a
substitute correctness contract. Randomness is zero and witness lines constant
in this delimited algebraic example; no BLC output distribution is claimed. -/
theorem detailed_prover_nonzero_constant (xi : F) (gamma : Fin 1 → F) :
    (proverArithmeticFlat (lambda := 128) [2, 2] xi 1 gamma
      (fun k => C (flatWitness k)) (fun _ => 0) columns).eval 0 ≠ 0 := by
  rw [PIOPArithmetic.verifier_evaluates_prover_flat]
  simp only [eval_C, eval_zero]
  rw [detailed_verifier_at_zero]
  exact neg_ne_zero.mpr one_ne_zero

end SDitH.Proofs.WitnessPIOPDiscrepancy
