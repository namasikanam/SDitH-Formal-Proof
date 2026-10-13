import SDitH.Spec.SDReduction
import SDitH.Proofs.PermutationProbability

namespace SDitH.Proofs.SDReduction

open Spec.SDReduction Spec.RegularSupport Spec.UniformChallenges
open scoped Classical BigOperators ENNReal

@[simp] theorem mem_vectorSupport {A F : Type*} [Fintype A] [Zero F]
    (x : A → F) (j : A) : j ∈ vectorSupport x ↔ x j ≠ 0 := by
  simp [vectorSupport]

theorem support_permute {A F : Type*} [Fintype A] [Zero F]
    (sigma : Equiv.Perm A) (x : A → F) :
    vectorSupport (permuteVector sigma x) = permute sigma (vectorSupport x) := by
  ext j
  simp only [mem_vectorSupport, permute, Finset.mem_image]
  constructor
  · intro hj
    exact ⟨sigma.symm j, hj, sigma.apply_symm_apply j⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [Spec.SDReduction.permuteVector] using ha

theorem support_weight {F : Type*} [Field F] {n : Nat} (x : Fin n → F) :
    (vectorSupport x).card = Spec.hammingWeight x := rfl

theorem permute_weight {F : Type*} [Field F] {n : Nat}
    (sigma : Equiv.Perm (Fin n)) (x : Fin n → F) :
    Spec.hammingWeight (permuteVector sigma x) = Spec.hammingWeight x := by
  rw [← support_weight, support_permute, RegularSupport.permute_card, support_weight]

theorem regular_iff_support {F : Type*} [Field F] {w m : Nat}
    (x : Coordinate w m → F) :
    Spec.Regular (fun i j => x (i, j)) ↔ Regular (vectorSupport x) := by
  constructor
  · intro h i
    obtain ⟨p, a, ha, hx⟩ := h i
    refine ⟨p, ?_, ?_⟩
    · change (i, p) ∈ vectorSupport x
      rw [mem_vectorSupport, show x (i, p) = a by
        simpa [Spec.elementary] using congrFun hx p]
      exact ha
    · intro j hj
      by_contra hjp
      have hz : x (i, j) = 0 := by simpa [Spec.elementary, hjp] using congrFun hx j
      exact (mem_vectorSupport x _).mp hj hz
  · intro h i
    obtain ⟨p, hp, huniq⟩ := h i
    refine ⟨p, x (i, p), (mem_vectorSupport x _).mp hp, ?_⟩
    funext j
    by_cases hj : j = p
    · simp [hj, Spec.elementary]
    · have hz : x (i, j) = 0 := by
        by_contra hn
        exact hj (huniq j ((mem_vectorSupport x _).mpr hn))
      simp [Spec.elementary, hj, hz]

theorem support_comp_equiv {A B F : Type*} [Fintype A] [Fintype B] [DecidableEq B] [Zero F]
    (e : A ≃ B) (x : B → F) :
    (vectorSupport (fun a => x (e a))).image e = vectorSupport x := by
  ext b
  simp [vectorSupport, Equiv.exists_congr_left e]

theorem regularFlat_weight {F : Type*} [Field F] {w m : Nat}
    (x : Fin (w * m) → F) (h : regularFlat x) : Spec.hammingWeight x = w := by
  have hr := (regular_iff_support (fun ij : Coordinate w m => x (finProdFinEquiv ij))).mp h
  have hc := RegularSupport.regular_card hr
  rw [← support_weight, ← support_comp_equiv finProdFinEquiv x]
  rw [Finset.card_image_of_injective _ (finProdFinEquiv (m := w) (n := m)).injective]
  exact hc

theorem permuted_mulVec {F : Type*} [Field F] {n k : Nat}
    (inst : Spec.SDInstance F n k) (sigma : Equiv.Perm (Fin n)) (x : Fin n → F) :
    (permuteInstance sigma inst).H.mulVec (permuteVector sigma x) = inst.H.mulVec x := by
  funext i
  exact Equiv.sum_comp sigma.symm (fun j => inst.H i j * x j)

theorem inverse_mulVec {F : Type*} [Field F] {n k : Nat}
    (inst : Spec.SDInstance F n k) (sigma : Equiv.Perm (Fin n)) (xhat : Fin n → F) :
    inst.H.mulVec (permuteVector sigma.symm xhat) =
      (permuteInstance sigma inst).H.mulVec xhat := by
  have h := permuted_mulVec inst sigma (permuteVector sigma.symm xhat)
  have hi : permuteVector sigma (permuteVector sigma.symm xhat) = xhat := by
    funext j
    simp [Spec.SDReduction.permuteVector]
  rw [hi] at h
  exact h.symm

theorem truncate_solution {F : Type*} [Field F] {n ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inst : Spec.SDInstance F n ksd) (x : Fin n → F)
    (h : inst.H.mulVec x = inst.y) :
    (truncate hkk inst).H.mulVec x = (truncate hkk inst).y := by
  funext i
  exact congrFun h (Fin.castLE (Nat.sub_le_sub_left hkk n) i)

theorem removed_row_count {n ksd krsd : Nat} (hkk : ksd ≤ krsd) (hkn : krsd ≤ n) :
    (n - ksd) - (n - krsd) = krsd - ksd := by omega

/-- A successful return satisfies the original syndrome equation. Weight is
inherited from the solver's candidate, not checked by A_sd itself. -/
theorem finish_some_iff {F : Type*} [Field F] {n k : Nat}
    (inst : Spec.SDInstance F n k) (sigma : Equiv.Perm (Fin n))
    (candidate : Option (Fin n → F)) (x : Fin n → F) :
    finish inst sigma candidate = some x ↔
      ∃ xhat, candidate = some xhat ∧
        (permuteInstance sigma inst).H.mulVec xhat = inst.y ∧
        permuteVector sigma.symm xhat = x := by
  cases candidate with
  | none => simp [finish]
  | some xhat => simp [finish, ite_eq_iff]

theorem finish_correct {F : Type*} [Field F] {w m k : Nat}
    (inst : Spec.SDInstance F (w * m) k) (sigma : Equiv.Perm (Fin (w * m)))
    (xhat x : Fin (w * m) → F) (hreg : regularFlat xhat)
    (hret : finish inst sigma (some xhat) = some x) : Spec.SDSolution inst w x := by
  obtain ⟨z, hz, hsyn, hout⟩ := (finish_some_iff inst sigma (some xhat) x).mp hret
  have hz' : xhat = z := Option.some.inj hz
  subst z
  subst x
  exact ⟨(inverse_mulVec inst sigma xhat).trans hsyn,
    (permute_weight sigma.symm xhat).trans (regularFlat_weight xhat hreg)⟩

/-- The deterministic uniqueness step: a full regular solution survives
truncation; if the truncated instance has only that regular solution, any
correct regular solver output passes the original syndrome check. -/
theorem unique_truncated_passes {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (inst : Spec.SDInstance F (w * m) ksd)
    (sigma : Equiv.Perm (Fin (w * m))) (witness xhat : Fin (w * m) → F)
    (hwit : RSDSolution (permuteInstance sigma inst) witness)
    (hout : RSDSolution (truncate hkk (permuteInstance sigma inst)) xhat)
    (hunique : ∀ a b,
      RSDSolution (truncate hkk (permuteInstance sigma inst)) a →
      RSDSolution (truncate hkk (permuteInstance sigma inst)) b → a = b) :
    finish inst sigma (some xhat) = some (permuteVector sigma.symm witness) := by
  have heq : xhat = witness := hunique xhat witness hout
    ⟨truncate_solution hkk (permuteInstance sigma inst) witness hwit.1, hwit.2⟩
  subst xhat
  simp [finish, show (permuteInstance sigma inst).H.mulVec witness = inst.y from hwit.1]

end SDitH.Proofs.SDReduction
