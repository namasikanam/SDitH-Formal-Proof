import SDitH.Spec.ProductOracle
import SDitH.Proofs.RandomOracleMention
import SDitH.Proofs.UniformVectors

/-! Component laws of the product-valued lazy oracle and the transferred
bounds: the matrix-component mask trap (table-dependent vector) has
probability at most budget*|F|^(-s), and a fresh digest component hits a
value mentioned by an earlier input with probability at most
choose(budget,2)*m/|D|. -/

namespace SDitH.Proofs.ProductOracle

open Spec.RandomOracleTrace Spec.RandomOracleTrap Spec.RandomOracleMention Spec.ProductOracle
open scoped Classical ENNReal BigOperators
noncomputable section

variable {Input D M State : Type*} [Fintype D] [Nonempty D] [Fintype M] [Nonempty M]

theorem uniform_fst : (PMF.uniformOfFintype (D × M)).map Prod.fst = PMF.uniformOfFintype D := by
  rw [← UniformVectors.uniform_pair, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hconst : ∀ a : D, (PMF.uniformOfFintype M).map (fun _ => a) = PMF.pure a := fun a => PMF.map_const _ _
  simp only [hconst]
  exact PMF.bind_pure _

theorem uniform_snd : (PMF.uniformOfFintype (D × M)).map Prod.snd = PMF.uniformOfFintype M := by
  rw [← UniformVectors.uniform_pair, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  rw [PMF.bind_const]
  exact PMF.map_id _

section Mask

variable {F : Type*} [Field F] [Fintype F] {s payload : Nat}

theorem uniform_mask_trap_le
    (vector : (Input → Option (D × Matrix (Fin s) (Fin payload) F)) → Input → Fin (s + payload) → F)
    (before : Input → Option (D × Matrix (Fin s) (Fin payload) F)) (input : Input) :
    ((PMF.uniformOfFintype (D × Matrix (Fin s) (Fin payload) F)).map (tableMaskTrap vector before input)) true ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ ^ s := by
  have hcomp : tableMaskTrap vector before input = kernelTrap (vector before) input ∘ Prod.snd := rfl
  rw [hcomp, ← PMF.map_comp, uniform_snd]
  exact RandomOracleTrap.uniform_kernel_trap_le (vector before) input

/-- Table-dependent mask trap bound on the product oracle. -/
theorem mask_trap_bound (procedure : Spec.RandomOracleCollision.Procedure Input (D × Matrix (Fin s) (Fin payload) F) State)
    (vector : (Input → Option (D × Matrix (Fin s) (Fin payload) F)) → Input → Fin (s + payload) → F)
    (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map (fun out => traceBad (tableMaskTrap vector) out.trace)) true ≤
      budget * (Fintype.card F : ℝ≥0∞)⁻¹ ^ s :=
  RandomOracleTrace.experiment_trace_bound procedure (tableMaskTrap vector) _
    (fun before input => uniform_mask_trap_le vector before input) budget initial

end Mask

theorem uniform_fst_mem_mass (S : Finset D) {inst : ∀ d, Decidable (d ∈ S)} :
    ((PMF.uniformOfFintype (D × M)).map (fun answer => @decide (answer.1 ∈ S) (inst answer.1))) true =
      (S.card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ := by
  have hcomp : (fun answer : D × M => @decide (answer.1 ∈ S) (inst answer.1)) =
      (fun d => @decide (d ∈ S) (inst d)) ∘ Prod.fst := rfl
  rw [hcomp, ← PMF.map_comp, uniform_fst, RandomOracleMention.uniform_mem_mass]

theorem digest_mention_query_bound (mentions : Input → Finset D) (m : Nat)
    (hm : ∀ input, (mentions input).card ≤ m) (log : List (Entry Input (D × M))) (input : Input) :
    ((PMF.uniformOfFintype (D × M)).map (digestMention mentions log input)) true ≤
      (log.length : ℝ≥0∞) * m * (Fintype.card D : ℝ≥0∞)⁻¹ := by
  have h := ChallengeMixtures.boolean_union_bound (PMF.uniformOfFintype (D × M))
    (digestMention mentions log input)
    (fun i : Fin log.length => fun answer => decide (answer.1 ∈ mentions (log[i]).input)) (by
      intro answer _ hhit
      obtain ⟨entry, hmem, he⟩ := List.any_eq_true.mp hhit
      obtain ⟨index, hlt, hindex⟩ := List.mem_iff_getElem.mp hmem
      exact ⟨⟨index, hlt⟩, by simpa only [Fin.getElem_fin, hindex] using he⟩)
  refine h.trans ?_
  calc
    _ ≤ ∑ _i : Fin log.length, (m : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      rw [uniform_fst_mem_mass]
      exact mul_le_mul_left (by exact_mod_cast hm (log[i]).input) _
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- A fresh digest component equals a value mentioned by an earlier fresh
input with probability at most choose(budget,2)*m/|D|. -/
theorem digest_mention_bound (procedure : Spec.RandomOracleCollision.Procedure Input (D × M) State)
    (mentions : Input → Finset D) (m : Nat) (hm : ∀ input, (mentions input).card ≤ m)
    (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map (fun out => prefixBad (digestMention mentions) out.trace)) true ≤
      (budget.choose 2 : ℝ≥0∞) * m * (Fintype.card D : ℝ≥0∞)⁻¹ := by
  have h := RandomOracleMention.experiment_prefix_bound procedure (digestMention mentions)
    (fun n => (n : ℝ≥0∞) * m * (Fintype.card D : ℝ≥0∞)⁻¹)
    (fun log input => digest_mention_query_bound mentions m hm log input) budget initial
  rw [RandomOracleMention.sum_range_mul] at h
  exact h

end
end SDitH.Proofs.ProductOracle
