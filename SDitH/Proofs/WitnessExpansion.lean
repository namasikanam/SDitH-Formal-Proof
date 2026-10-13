import SDitH.Spec.WitnessExpansion
import SDitH.Proofs.Tensor
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

namespace SDitH.Proofs.WitnessExpansion

open Spec Spec.WitnessExpansion
open scoped BigOperators

theorem radixSize_eq_prod {d : Nat} (width : Fin d → Nat) :
    radixSize width = ∏ j, (width j + 1) := by
  induction d with
  | zero => simp [radixSize]
  | succ d ih => simp [radixSize, Fin.prod_univ_succ, ih]

theorem radixSize_pos {d : Nat} (width : Fin d → Nat) : 0 < radixSize width := by
  rw [radixSize_eq_prod]
  exact Finset.prod_pos (fun _ _ => Nat.zero_lt_succ _)

theorem remaining_eq_div {d : Nat} (width : Fin d → Nat) (position : Nat) :
    (splitPosition width position).remaining = position / radixSize width := by
  induction d generalizing position with
  | zero => simp [splitPosition, radixSize]
  | succ d ih => simp [splitPosition, radixSize, ih, Nat.div_div_eq_div_mul]

/-- The mixed-radix loop preserves the whole original position, including an
explicit unprocessed quotient if the input exceeds the tensor size. -/
theorem split_reconstruction {d : Nat} (width : Fin d → Nat) (position : Nat) :
    joinDigits width (splitPosition width position).digits +
      radixSize width * (splitPosition width position).remaining = position := by
  induction d generalizing position with
  | zero => simp [splitPosition, joinDigits, radixSize]
  | succ d ih =>
    simp only [splitPosition, joinDigits, Fin.cases_zero, Fin.cases_succ, radixSize]
    have h := ih (fun j => width j.succ) (position / (width 0 + 1))
    calc
      _ = position % (width 0 + 1) + (width 0 + 1) *
          (joinDigits (fun j => width j.succ)
              (splitPosition (fun j => width j.succ) (position / (width 0 + 1))).digits +
            radixSize (fun j => width j.succ) *
              (splitPosition (fun j => width j.succ) (position / (width 0 + 1))).remaining) := by ring
      _ = position % (width 0 + 1) + (width 0 + 1) * (position / (width 0 + 1)) := by rw [h]
      _ = position := Nat.mod_add_div _ _

theorem split_bounded {d : Nat} (width : Fin d → Nat) (position : Nat)
    (hp : position < radixSize width) :
    (splitPosition width position).remaining = 0 ∧
      joinDigits width (splitPosition width position).digits = position := by
  have hr : (splitPosition width position).remaining = 0 := by
    rw [remaining_eq_div, Nat.div_eq_of_lt hp]
  exact ⟨hr, by simpa [hr] using split_reconstruction width position⟩

theorem split_digits_injective_below_size {d : Nat} (width : Fin d → Nat)
    (a b : Nat) (ha : a < radixSize width) (hb : b < radixSize width)
    (h : (splitPosition width a).digits = (splitPosition width b).digits) : a = b := by
  rw [← (split_bounded width a ha).2, ← (split_bounded width b hb).2, h]

theorem joinDigits_lt_size {d : Nat} (width : Fin d → Nat)
    (digits : (j : Fin d) → Fin (width j + 1)) :
    joinDigits width digits < radixSize width := by
  induction d with
  | zero => simp [joinDigits, radixSize]
  | succ d ih =>
    simp only [joinDigits, radixSize]
    have hhead := (digits 0).isLt
    have htail := ih (fun j => width j.succ) (fun j => digits j.succ)
    nlinarith

theorem split_joinDigits {d : Nat} (width : Fin d → Nat)
    (digits : (j : Fin d) → Fin (width j + 1)) :
    (splitPosition width (joinDigits width digits)).digits = digits := by
  induction d with
  | zero => funext j; exact Fin.elim0 j
  | succ d ih =>
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · apply Fin.ext
      simp [splitPosition, joinDigits, Nat.mod_eq_of_lt (digits 0).isLt]
    · simp only [splitPosition, joinDigits, Fin.cases_succ]
      rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_succ _), Nat.div_eq_of_lt (digits 0).isLt,
        Nat.zero_add, ih]

variable {F : Type*} [Field F]

/-- The last-coordinate omission is lossless for elementary vectors, exactly
with the source's last-coordinate complement convention. -/
theorem complete_omitted_elementary {r : Nat} (position : Fin (r + 1)) :
    completeSelector (F := F) (fun k : Fin r => elementary position k.castSucc) =
      elementary position := by
  classical
  have hs : (∑ k : Fin (r + 1), elementary (F := F) position k) = 1 := by
    calc
      _ = ∑ k : Fin (r + 1), if k = position then (1 : F) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : k = position <;> simp [elementary, h]
      _ = 1 := Finset.sum_ite_eq_of_mem' Finset.univ position (fun _ => (1 : F))
        (Finset.mem_univ position)
  rw [Fin.sum_univ_castSucc] at hs
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [completeSelector, Fin.lastCases_last]
    linear_combination -hs
  · simp [completeSelector]

theorem completed_selector {d : Nat} (width : Fin d → Nat) (position : Nat) (j : Fin d) :
    completeSelector (selector (F := F) width position j) =
      elementary ((splitPosition width position).digits j) := by
  exact complete_omitted_elementary _

theorem elementary_injective {I : Type*} (p q : I)
    (h : elementary (F := F) p = elementary q) : p = q := by
  classical
  by_contra hpq
  have he := congrFun h p
  simp [elementary, hpq] at he

theorem omitted_elementary_injective {r : Nat} (p q : Fin (r + 1))
    (h : (fun k : Fin r => elementary (F := F) p k.castSucc) =
      (fun k : Fin r => elementary q k.castSucc)) : p = q := by
  apply elementary_injective (F := F) p q
  simpa only [complete_omitted_elementary] using congrArg completeSelector h

/-- The stored tensor, when read in the explicit order inverse to line 9,
selects precisely the sampled coordinate. -/
theorem completed_tensor_coordinate {d : Nat} (width : Fin d → Nat)
    (position : Nat) (hp : position < radixSize width)
    (coordinate : (j : Fin d) → Fin (width j + 1)) :
    tensor (F := F) (fun j => completeSelector (selector width position j)) coordinate =
      if joinDigits width coordinate = position then 1 else 0 := by
  classical
  simp only [completed_selector]
  rw [tensor_elementary]
  unfold elementary
  have he : coordinate = (splitPosition width position).digits ↔
      joinDigits width coordinate = position := by
    constructor
    · intro h; rw [h]; exact (split_bounded width position hp).2
    · intro h
      rw [← split_joinDigits width coordinate, h]
  simp only [he]

theorem witnessLoop_length {d : Nat} (width : Fin d → Nat) (position : Nat) :
    (witnessLoop (F := F) width position).length = ∑ j, width j := by
  induction d generalizing position with
  | zero => simp [witnessLoop]
  | succ d ih => simp [witnessLoop, ih, Fin.sum_univ_succ]

theorem witnessLoop_eq_selectors {d : Nat} (width : Fin d → Nat) (position : Nat) :
    witnessLoop (F := F) width position =
      (List.ofFn (fun j => List.ofFn (selector (F := F) width position j))).flatten := by
  classical
  induction d generalizing position with
  | zero => simp [witnessLoop]
  | succ d ih =>
    rw [witnessLoop, ih, List.ofFn_succ, List.flatten_cons]
    congr 1
    · congr 1
      funext k
      simp [selector, splitPosition, elementary, Fin.ext_iff]

theorem expansion_witness_length {w m d : Nat} (width : Fin d → Nat)
    (positions : Fin w → Fin m) :
    (expandAfterSampling (F := F) width positions).witness.length = w * ∑ j, width j := by
  simp [expandAfterSampling, List.length_flatten, List.map_ofFn, witnessLoop_length,
    List.sum_ofFn]

theorem expansion_solution_coordinate {w m d : Nat} (width : Fin d → Nat)
    (positions : Fin w → Fin m) (i : Fin w) (j : Fin m) :
    (expandAfterSampling (F := F) width positions).solution (finProdFinEquiv (i, j)) =
      elementary (positions i) j := by
  change elementary (positions (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = _
  rw [Equiv.symm_apply_apply]

theorem expansion_binary_regular {w m d : Nat} (width : Fin d → Nat)
    (positions : Fin w → Fin m) :
    BinaryRegular (fun i j =>
      (expandAfterSampling (F := ZMod 2) width positions).solution (finProdFinEquiv (i, j))) := by
  intro i
  exact ⟨positions i, funext (fun j => expansion_solution_coordinate width positions i j)⟩

/-- The flattened solution has exactly one nonzero coordinate per original
chunk. This is independent of the tensor dimension equation and the sampler's
distribution. -/
theorem expansion_weight {w m d : Nat} (width : Fin d → Nat)
    (positions : Fin w → Fin m) :
    hammingWeight (expandAfterSampling (F := F) width positions).solution = w := by
  classical
  let address : Fin w → Fin (w * m) := fun i => finProdFinEquiv (i, positions i)
  have hinj : Function.Injective address := by
    intro a b h
    exact congrArg Prod.fst (finProdFinEquiv.injective h)
  have hs : Finset.univ.filter
      (fun a => (expandAfterSampling (F := F) width positions).solution a ≠ 0) =
      Finset.univ.image address := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have he : (finProdFinEquiv.symm a).2 = positions (finProdFinEquiv.symm a).1 := by
        by_contra hn
        change a.modNat ≠ positions a.divNat at hn
        exact h (by simp [expandAfterSampling, elementary, hn])
      refine ⟨(finProdFinEquiv.symm a).1, ?_⟩
      dsimp [address]
      change a.modNat = positions a.divNat at he
      rw [← he]
      exact finProdFinEquiv.apply_symm_apply a
    · rintro ⟨i, rfl⟩
      simp [address, expansion_solution_coordinate, elementary]
  unfold hammingWeight
  rw [hs, Finset.card_image_of_injective _ hinj]
  exact Finset.card_fin w

/-- Equality of the actual appended witness lists determines the sampled
position whenever both lie in the representable mixed-radix range. -/
theorem witnessLoop_injective_below_size {d : Nat} (width : Fin d → Nat)
    (a b : Nat) (ha : a < radixSize width) (hb : b < radixSize width)
    (h : witnessLoop (F := F) width a = witnessLoop width b) : a = b := by
  classical
  induction d generalizing a b with
  | zero => simp only [radixSize] at ha hb; omega
  | succ d ih =>
    simp only [witnessLoop] at h
    have hfirst := List.append_inj_left h (by simp)
    have htail := List.append_inj_right h (by simp)
    have hvec := List.ofFn_injective hfirst
    have hhead : a % (width 0 + 1) = b % (width 0 + 1) := by
      let p : Fin (width 0 + 1) := ⟨a % (width 0 + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
      let q : Fin (width 0 + 1) := ⟨b % (width 0 + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
      have hv : (fun k : Fin (width 0) => elementary (F := F) p k.castSucc) =
          (fun k : Fin (width 0) => elementary (F := F) q k.castSucc) := by
        funext k
        have he := congrFun hvec k
        simpa [elementary, p, q, Fin.ext_iff] using he
      exact congrArg Fin.val (omitted_elementary_injective p q hv)
    have ha' : a / (width 0 + 1) < radixSize (fun j => width j.succ) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ _)).mpr
      simpa [radixSize, Nat.mul_comm] using ha
    have hb' : b / (width 0 + 1) < radixSize (fun j => width j.succ) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ _)).mpr
      simpa [radixSize, Nat.mul_comm] using hb
    have hquot := ih (fun j => width j.succ) _ _ ha' hb' htail
    have haeq := Nat.mod_add_div a (width 0 + 1)
    have hbeq := Nat.mod_add_div b (width 0 + 1)
    rw [hhead, hquot] at haeq
    omega

/-- The entire transmitted witness, including its outer chunk concatenation,
uniquely determines the sampled positions on the stated representable range. -/
theorem expansion_witness_injective {w m d : Nat} (width : Fin d → Nat)
    (hm : m ≤ radixSize width) (a b : Fin w → Fin m)
    (h : (expandAfterSampling (F := F) width a).witness =
      (expandAfterSampling (F := F) width b).witness) : a = b := by
  have hl : List.ofFn (fun i => witnessLoop (F := F) width (a i).val) =
      List.ofFn (fun i => witnessLoop (F := F) width (b i).val) := by
    apply List.eq_iff_flatten_eq.mpr
    exact ⟨h, by simp [List.map_ofFn, Function.comp_def, witnessLoop_length]⟩
  have hv := List.ofFn_injective hl
  funext i
  apply Fin.ext
  exact witnessLoop_injective_below_size width _ _
    ((a i).isLt.trans_le hm) ((b i).isLt.trans_le hm) (congrFun hv i)

/-- Sampled binary positions fit in their mixed-radix encodings. This weaker
inequality is compatible with, and does not repair, the proved failure of the
required equality between tensor size and source chunk size. -/
theorem table3_position_ranges_fit :
    (let p := RSDParameters.categoryI; p.n / p.w ≤ radixSize (parameterWidths p)) ∧
    (let p := RSDParameters.categoryIII; p.n / p.w ≤ radixSize (parameterWidths p)) ∧
    (let p := RSDParameters.categoryV; p.n / p.w ≤ radixSize (parameterWidths p)) := by decide

/-- The table rows do have whole chunks and positive arities. No hidden rounding
is required for the size of the flat solution produced by Algorithm 1. -/
theorem table3_chunk_sizes :
    (let p := RSDParameters.categoryI; p.w * (p.n / p.w) = p.n ∧ ∀ a ∈ p.arities, 0 < a) ∧
    (let p := RSDParameters.categoryIII; p.w * (p.n / p.w) = p.n ∧ ∀ a ∈ p.arities, 0 < a) ∧
    (let p := RSDParameters.categoryV; p.w * (p.n / p.w) = p.n ∧ ∀ a ∈ p.arities, 0 < a) := by decide

end SDitH.Proofs.WitnessExpansion
