import SDitH.Spec.RegularSupport
import SDitH.Proofs.UniformChallenges
import Mathlib.Logic.Equiv.Fintype

namespace SDitH.Proofs.RegularSupport

open Spec.RegularSupport Spec.UniformChallenges
open scoped Classical ENNReal

@[simp] theorem mem_graph {w m : Nat} (positions : Fin w → Fin m)
    (i : Fin w) (j : Fin m) : (i, j) ∈ graph positions ↔ j = positions i := by
  simp [graph, Prod.ext_iff, eq_comm]

theorem graph_card {w m : Nat} (positions : Fin w → Fin m) :
    (graph positions).card = w := by
  rw [graph, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

theorem graph_regular {w m : Nat} (positions : Fin w → Fin m) :
    Regular (graph positions) := by
  intro i
  exact ⟨positions i, (mem_graph positions i _).mpr rfl,
    fun j hj => (mem_graph positions i j).mp hj⟩

theorem regular_iff_graph {w m : Nat} (support : Finset (Coordinate w m)) :
    Regular support ↔ ∃ positions, support = graph positions := by
  constructor
  · intro h
    choose p hp using fun i => ExistsUnique.exists (h i)
    refine ⟨p, ?_⟩
    ext ⟨i, j⟩
    rw [mem_graph]
    exact ⟨fun hj => ExistsUnique.unique (h i) hj (hp i), fun hj => hj ▸ hp i⟩
  · rintro ⟨p, rfl⟩
    exact graph_regular p

theorem graph_injective {w m : Nat} :
    Function.Injective (graph (w := w) (m := m)) := by
  intro p q h
  funext i
  have hi : (i, p i) ∈ graph q := h ▸ (mem_graph p i _).mpr rfl
  exact (mem_graph q i _).mp hi

theorem regular_card {w m : Nat} {support : Finset (Coordinate w m)}
    (h : Regular support) : support.card = w := by
  obtain ⟨p, rfl⟩ := (regular_iff_graph support).mp h
  exact graph_card p

@[simp] theorem mem_weightSupports {w m : Nat} (support : Finset (Coordinate w m)) :
    support ∈ weightSupports w m ↔ support.card = w := by
  simp [weightSupports]

theorem weightSupports_card (w m : Nat) :
    (weightSupports w m).card = Nat.choose (w * m) w := by
  simp [weightSupports, Coordinate]

theorem regular_support_count (w m : Nat) :
    ((weightSupports w m).filter Regular).card = m ^ w := by
  have h : (weightSupports w m).filter Regular =
      Finset.univ.image (graph (w := w) (m := m)) := by
    ext support
    simp only [Finset.mem_filter, mem_weightSupports, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · intro hs
      obtain ⟨p, hp⟩ := (regular_iff_graph support).mp hs.2
      exact ⟨p, hp.symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨graph_card p, graph_regular p⟩
  rw [h, Finset.card_image_of_injective _ graph_injective]
  simp

theorem weightSupports_nonempty (w m : Nat) (hm : 0 < m) :
    (weightSupports w m).Nonempty := by
  exact ⟨graph (fun _ => ⟨0, hm⟩), (mem_weightSupports _).mpr (graph_card _)⟩

/-- Exact counting law for a uniformly chosen weight-w support. -/
theorem regular_support_probability (w m : Nat) (hm : 0 < m) :
    subsetProbability (weightSupports w m) (weightSupports_nonempty w m hm) Regular =
      (m ^ w : ℝ≥0∞) / Nat.choose (w * m) w := by
  rw [UniformChallenges.subset_probability_card, regular_support_count, weightSupports_card]
  norm_cast

@[simp] theorem permute_card {A : Type*} (sigma : Equiv.Perm A) (s : Finset A) :
    (permute sigma s).card = s.card :=
  Finset.card_image_of_injective _ sigma.injective

theorem permute_trans {A : Type*} (sigma tau : Equiv.Perm A) (s : Finset A) :
    permute tau (permute sigma s) = permute (sigma.trans tau) s := by
  simp [permute, Finset.image_image]

@[simp] theorem permute_refl {A : Type*} (s : Finset A) :
    permute (Equiv.refl A) s = s := by simp [permute]

/-- Any two equal-size supports are related by an ambient permutation. -/
theorem exists_permute_eq {A : Type*} [Fintype A] (s t : Finset A)
    (h : s.card = t.card) : ∃ sigma : Equiv.Perm A, permute sigma s = t := by
  let e : {x // x ∈ s} ≃ {x // x ∈ t} :=
    Fintype.equivOfCardEq (by simpa using h)
  refine ⟨e.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact e.extendSubtype_mem a ha
  · simpa using h.ge

end SDitH.Proofs.RegularSupport
