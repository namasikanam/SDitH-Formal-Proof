import SDitH.Proofs.IdealCipherPairProbability
import SDitH.Proofs.IdealCipherComparison

/-! A key whose two paired inputs are both unobserved matches two given
target outputs with probability at most 1/(M-q) * 1/(M-(q+1)) under the
posterior family law, and some such key among a set of size k does so with
probability at most k times that. This is the ideal-cipher step for a seed
collision against an unqueried seed; collisions among queried seeds are the
already bounded witnessed pair event. -/

namespace SDitH.Proofs.IdealCipherUnseenMatch

open Spec.IdealCipher Spec.IdealCipherPairCollision IdealCipherFresh
open scoped Classical ENNReal BigOperators
noncomputable section

variable {Key Block : Type*} [Fintype Key] [Fintype Block]

theorem target_card_one (a : Block) : Fintype.card {output : Block // id output = a} ≤ 1 := by
  have : Fintype.card {output : Block // id output = a} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨a, rfl⟩, fun y => Subtype.ext y.property⟩
  omega

/-- Both unobserved inputs of one key match given targets. -/
theorem unseen_double_match_bound (world : World Key Block) (key : Key) (x : Block) (a b : Block)
    (companion : Block → Block) (hcomp : companion x ≠ x)
    (hfresh1 : FreshInput world key x) (hfresh2 : FreshInput world key (companion x))
    (q : Nat) (hlen : world.history.length ≤ q) :
    ((PMF.uniformOfFintype (Candidates world)).map
      (fun family => decide (family.val key x = a ∧ family.val key (companion x) = b))) true ≤
      ((1 : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞)) *
        ((1 : ℝ≥0∞) / ((Fintype.card Block - (q + 1) : Nat) : ℝ≥0∞)) := by
  let test : Block → List (Entry Key Block) → Family Key Block → PMF Bool :=
    fun value _ family => PMF.pure (decide (value = a ∧ family key (companion x) = b))
  have he := IdealCipher.posterior_step world (.encrypt key x) test
  change ((PMF.uniformOfFintype (Candidates world)).bind (fun family =>
    test (answer family.val (.encrypt key x)) (entry (.encrypt key x) (answer family.val (.encrypt key x)) :: world.history) family.val)) true ≤ _
  rw [← he]
  apply (IdealCipherPairProbability.bind_gate_bound _ _ (fun sample => answer sample.val (.encrypt key x) = a)
    ((1 : ℝ≥0∞) / ((Fintype.card Block - (q + 1) : Nat) : ℝ≥0∞)) ?_).trans
  · apply mul_le_mul_left
    have h := IdealCipherComparison.family_target_bound world key x hfresh1 q hlen id a 1 (target_card_one a)
    simpa only [id, Nat.cast_one] using h
  · intro sample
    by_cases hg : answer sample.val (.encrypt key x) = a
    · rw [if_pos hg]
      simp only [test, hg, true_and]
      have hobs := IdealCipherComparison.fresh_observe world (.encrypt key x) (answer sample.val (.encrypt key x))
        ⟨sample.val, sample.property, rfl⟩ key (companion x) hfresh2 (Or.inr (by
          change x ≠ companion x
          exact hcomp.symm))
      have h := IdealCipherComparison.family_target_bound
        (observe world (.encrypt key x) (answer sample.val (.encrypt key x)) ⟨sample.val, sample.property, rfl⟩)
        key (companion x) hobs (q + 1) (by simp [observe, hlen]) id b 1 (target_card_one b)
      simpa only [id, Nat.cast_one, PMF.bind_pure_comp] using h
    · rw [if_neg hg]
      simp [test, hg]

/-- Some key in a finite set, all of whose paired inputs are unobserved,
matches the targets with probability at most the set size times the bound. -/
theorem exists_unseen_double_match_bound (world : World Key Block) (keys : Finset Key) (x : Block) (a b : Block)
    (companion : Block → Block) (hcomp : companion x ≠ x)
    (hfresh : ∀ key ∈ keys, FreshInput world key x ∧ FreshInput world key (companion x))
    (q : Nat) (hlen : world.history.length ≤ q) :
    ((PMF.uniformOfFintype (Candidates world)).map
      (fun family => decide (∃ key ∈ keys, family.val key x = a ∧ family.val key (companion x) = b))) true ≤
      (keys.card : ℝ≥0∞) * (((1 : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞)) *
        ((1 : ℝ≥0∞) / ((Fintype.card Block - (q + 1) : Nat) : ℝ≥0∞))) := by
  have h := ChallengeMixtures.boolean_union_bound (PMF.uniformOfFintype (Candidates world))
    (fun family => decide (∃ key ∈ keys, family.val key x = a ∧ family.val key (companion x) = b))
    (fun key : keys => fun family => decide (family.val key.val x = a ∧ family.val key.val (companion x) = b)) (by
      intro family _ hhit
      obtain ⟨key, hkey, hmatch⟩ := of_decide_eq_true hhit
      exact ⟨⟨key, hkey⟩, decide_eq_true hmatch⟩)
  refine h.trans ?_
  calc
    _ ≤ ∑ _key : keys, ((1 : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞)) *
        ((1 : ℝ≥0∞) / ((Fintype.card Block - (q + 1) : Nat) : ℝ≥0∞)) := by
      apply Finset.sum_le_sum
      intro key _
      exact unseen_double_match_bound world key.val x a b companion hcomp (hfresh key.val key.property).1
        (hfresh key.val key.property).2 q hlen
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

end
end SDitH.Proofs.IdealCipherUnseenMatch
