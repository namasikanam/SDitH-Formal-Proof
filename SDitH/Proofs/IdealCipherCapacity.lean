import SDitH.Proofs.IdealCipherInverse

namespace SDitH.Proofs.IdealCipherCapacity

open Spec.IdealCipher IdealCipherFresh IdealCipherInverse
open scoped Classical ENNReal
noncomputable section

variable {Key Block : Type*} [Fintype Block]

theorem unusedOutput_card_lower (world : World Key Block) (key : Key) :
    Fintype.card Block - world.history.length ≤ Fintype.card (UnusedOutput world key) := by
  have hs : Finset.univ.filter (fun output => ¬ FreshOutput world key output) ⊆
      (world.history.map Entry.output).toFinset := by
    intro output houtput
    have hn : ¬ FreshOutput world key output := (Finset.mem_filter.mp houtput).2
    by_contra hmem
    apply hn
    intro e he _ heq
    apply hmem
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, heq⟩)
  have hused : Fintype.card {output : Block // ¬ FreshOutput world key output} ≤ world.history.length := by
    calc
      _ = (Finset.univ.filter (fun output => ¬ FreshOutput world key output)).card := Fintype.card_subtype _
      _ ≤ (world.history.map Entry.output).toFinset.card := Finset.card_le_card hs
      _ ≤ (world.history.map Entry.output).length := List.toFinset_card_le _
      _ = _ := List.length_map _
  have hc : Fintype.card (UnusedOutput world key) =
      Fintype.card Block - Fintype.card {output : Block // ¬ FreshOutput world key output} := by
    simpa only [not_not] using Fintype.card_subtype_compl (fun output => ¬ FreshOutput world key output)
  rw [hc]
  exact Nat.sub_le_sub_left hused _

theorem unusedInput_card_lower (world : World Key Block) (key : Key) :
    Fintype.card Block - world.history.length ≤ Fintype.card (UnusedInput world key) := by
  have h := unusedOutput_card_lower (reverseWorld world) key
  rw [Fintype.card_congr (unusedInverseEquiv world key)] at h
  simpa only [reverseWorld, List.length_map] using h

variable [Fintype Key]

theorem fresh_encrypt_event_budget_bound (world : World Key Block) (key : Key) (input : Block)
    (hfresh : FreshInput world key input) (q : Nat) (hlen : world.history.length ≤ q) (event : Block → Prop) :
    ((query world (.encrypt key input)).map (fun result => decide (event result.1))) true ≤
      (Fintype.card {output : Block // event output} : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞) := by
  apply (fresh_encrypt_event_bound world key input hfresh event).trans
  apply ENNReal.div_le_div_left
  exact_mod_cast (Nat.sub_le_sub_left hlen (Fintype.card Block)).trans (unusedOutput_card_lower world key)

theorem fresh_decrypt_event_budget_bound (world : World Key Block) (key : Key) (output : Block)
    (hfresh : FreshOutput world key output) (q : Nat) (hlen : world.history.length ≤ q) (event : Block → Prop) :
    ((query world (.decrypt key output)).map (fun result => decide (event result.1))) true ≤
      (Fintype.card {input : Block // event input} : ℝ≥0∞) / ((Fintype.card Block - q : Nat) : ℝ≥0∞) := by
  apply (fresh_decrypt_event_bound world key output hfresh event).trans
  apply ENNReal.div_le_div_left
  exact_mod_cast (Nat.sub_le_sub_left hlen (Fintype.card Block)).trans (unusedInput_card_lower world key)

theorem fresh_encrypt_target_budget_bound (world : World Key Block) (key : Key) (input target : Block)
    (hfresh : FreshInput world key input) (q : Nat) (hlen : world.history.length ≤ q) :
    ((query world (.encrypt key input)).map (fun result => decide (result.1 = target))) true ≤
      ((Fintype.card Block - q : Nat) : ℝ≥0∞)⁻¹ := by
  simpa using fresh_encrypt_event_budget_bound world key input hfresh q hlen (fun output => output = target)

theorem fresh_decrypt_target_budget_bound (world : World Key Block) (key : Key) (output target : Block)
    (hfresh : FreshOutput world key output) (q : Nat) (hlen : world.history.length ≤ q) :
    ((query world (.decrypt key output)).map (fun result => decide (result.1 = target))) true ≤
      ((Fintype.card Block - q : Nat) : ℝ≥0∞)⁻¹ := by
  simpa using fresh_decrypt_event_budget_bound world key output hfresh q hlen (fun input => input = target)

end
end SDitH.Proofs.IdealCipherCapacity
