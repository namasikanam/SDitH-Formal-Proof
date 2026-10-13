import SDitH.Proofs.IdealCipher
import SDitH.Proofs.UniformSymmetry

namespace SDitH.Proofs.IdealCipherFresh

open Spec.IdealCipher
open scoped Classical ENNReal
noncomputable section

variable {Key Block : Type*}

def FreshInput (world : World Key Block) (key : Key) (input : Block) : Prop :=
  ∀ e ∈ world.history, e.key = key → e.input ≠ input

def FreshOutput (world : World Key Block) (key : Key) (output : Block) : Prop :=
  ∀ e ∈ world.history, e.key = key → e.output ≠ output

abbrev UnusedOutput (world : World Key Block) (key : Key) := {output : Block // FreshOutput world key output}

def freshImage (world : World Key Block) (key : Key) (input : Block) (hfresh : FreshInput world key input)
    (family : Candidates world) : UnusedOutput world key :=
  ⟨family.val key input, by
    intro e he hk ho
    have hold : family.val key e.input = e.output := by simpa only [hk] using family.property e he
    exact hfresh e he hk ((family.val key).injective (hold.trans ho))⟩

theorem unusedOutput_nonempty (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) : Nonempty (UnusedOutput world key) :=
  ⟨freshImage world key input hfresh (Classical.choice (candidates_nonempty world))⟩

def swapFamily (family : Family Key Block) (key : Key) (left right : Block) : Family Key Block :=
  Function.update family key ((family key).trans (Equiv.swap left right))

theorem swap_matches (world : World Key Block) (key : Key) (left right : UnusedOutput world key)
    (family : Candidates world) : Matches (swapFamily family.val key left.val right.val) world.history := by
  intro e he
  by_cases hk : e.key = key
  · have hold : family.val key e.input = e.output := by simpa only [hk] using family.property e he
    change (Function.update family.val key ((family.val key).trans (Equiv.swap left.val right.val)) e.key) e.input = e.output
    rw [hk, Function.update_self]
    change Equiv.swap left.val right.val (family.val key e.input) = e.output
    rw [hold]
    exact Equiv.swap_apply_of_ne_of_ne (left.property e he hk) (right.property e he hk)
  · simpa only [swapFamily, Function.update_of_ne hk] using family.property e he

def swapCandidates (world : World Key Block) (key : Key) (left right : UnusedOutput world key) :
    Candidates world ≃ Candidates world :=
  Function.Involutive.toPerm (fun family => ⟨swapFamily family.val key left.val right.val,
    swap_matches world key left right family⟩) (by
      intro family
      apply Subtype.ext
      funext other
      by_cases hk : other = key
      · subst other
        apply Equiv.ext
        intro input
        simp [swapFamily, Equiv.trans_apply]
      · simp [swapFamily, Function.update_of_ne hk])

theorem freshImage_swap (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) (left right : UnusedOutput world key) (family : Candidates world) :
    freshImage world key input hfresh (swapCandidates world key left right family) =
      Equiv.swap left right (freshImage world key input hfresh family) := by
  apply Subtype.ext
  change (swapFamily family.val key left.val right.val key) input =
    (Equiv.swap left right (freshImage world key input hfresh family)).val
  rw [swapFamily, Function.update_self]
  change Equiv.swap left.val right.val (family.val key input) =
    (Equiv.swap left right (freshImage world key input hfresh family)).val
  exact (Subtype.val_injective.map_swap left right (freshImage world key input hfresh family)).symm

variable [Fintype Key] [Fintype Block]

/-- Conditional on the entire transcript, a fresh encryption answer is uniform
over unused ciphertexts at that key. All prior decryptions are included. -/
theorem fresh_image_uniform (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) :
    letI : Nonempty (UnusedOutput world key) := unusedOutput_nonempty world key input hfresh
    (PMF.uniformOfFintype (Candidates world)).map (freshImage world key input hfresh) =
      PMF.uniformOfFintype (UnusedOutput world key) := by
  letI : Nonempty (UnusedOutput world key) := unusedOutput_nonempty world key input hfresh
  exact UniformSymmetry.uniform_map_of_swaps _ (swapCandidates world key)
    (freshImage_swap world key input hfresh)

theorem fresh_encrypt_uniform (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) :
    letI : Nonempty (UnusedOutput world key) := unusedOutput_nonempty world key input hfresh
    (query world (.encrypt key input)).map Prod.fst =
      (PMF.uniformOfFintype (UnusedOutput world key)).map Subtype.val := by
  letI : Nonempty (UnusedOutput world key) := unusedOutput_nonempty world key input hfresh
  rw [← fresh_image_uniform world key input hfresh]
  simp only [query, PMF.map_comp, Function.comp_def]
  rfl

/-- A projected-output event can include at most its full-block fiber size.
This accounts for truncation without treating the projection as a permutation. -/
theorem fresh_encrypt_event_bound (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) (event : Block → Prop) :
    ((query world (.encrypt key input)).map (fun result => decide (event result.1))) true ≤
      (Fintype.card {output : Block // event output} : ℝ≥0∞) /
        (Fintype.card (UnusedOutput world key) : ℝ≥0∞) := by
  letI : Nonempty (UnusedOutput world key) := unusedOutput_nonempty world key input hfresh
  have hcard : Fintype.card {output : UnusedOutput world key // event output.val} ≤
      Fintype.card {output : Block // event output} :=
    Fintype.card_le_of_injective (fun output => (⟨output.val.val, output.property⟩ : {output : Block // event output}))
      (by
        intro a b h
        exact Subtype.ext (Subtype.ext (congrArg (fun x : {output : Block // event output} => x.val) h)))
  calc
    _ = ((query world (.encrypt key input)).map Prod.fst).toOuterMeasure {output | event output} := by
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
      congr 1
      ext result
      simp
    _ = (PMF.uniformOfFintype (UnusedOutput world key)).toOuterMeasure {output | event output.val} := by
      rw [fresh_encrypt_uniform world key input hfresh, PMF.toOuterMeasure_map_apply]
      rfl
    _ = (Fintype.card {output : UnusedOutput world key // event output.val} : ℝ≥0∞) /
        (Fintype.card (UnusedOutput world key) : ℝ≥0∞) := PMF.toOuterMeasure_uniformOfFintype_apply _
    _ ≤ _ := by
      exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

end
end SDitH.Proofs.IdealCipherFresh
