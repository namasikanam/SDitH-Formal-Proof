import SDitH.Proofs.IdealCipherFresh

namespace SDitH.Proofs.IdealCipherInverse

open Spec.IdealCipher IdealCipherFresh
open scoped Classical ENNReal
noncomputable section

variable {Key Block : Type*}

def flipEntry (e : Entry Key Block) : Entry Key Block := ⟨e.key, e.output, e.input⟩

theorem matches_inverse (family : Family Key Block) (history : List (Entry Key Block)) (h : Matches family history) :
    Matches (fun key => (family key).symm) (history.map flipEntry) := by
  intro e he
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp he
  change (family old.key).symm old.output = old.input
  rw [← h old hold, Equiv.symm_apply_apply]

def reverseWorld (world : World Key Block) : World Key Block :=
  ⟨world.history.map flipEntry, by
    obtain ⟨family, h⟩ := world.possible
    exact ⟨fun key => (family key).symm, matches_inverse family world.history h⟩⟩

def inverseCandidates (world : World Key Block) : Candidates world ≃ Candidates (reverseWorld world) where
  toFun family := ⟨fun key => (family.val key).symm, matches_inverse family.val world.history family.property⟩
  invFun family := ⟨fun key => (family.val key).symm, by
    intro e he
    have h := family.property (flipEntry e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    change family.val e.key e.output = e.input at h
    change (family.val e.key).symm e.input = e.output
    rw [← h, Equiv.symm_apply_apply]⟩
  left_inv family := by apply Subtype.ext; funext key; rfl
  right_inv family := by apply Subtype.ext; funext key; rfl

abbrev UnusedInput (world : World Key Block) (key : Key) := {input : Block // FreshInput world key input}

theorem reverse_fresh_input (world : World Key Block) (key : Key) (output : Block)
    (h : FreshOutput world key output) : FreshInput (reverseWorld world) key output := by
  intro e he hk
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp he
  exact h old hold hk

def unusedInverseEquiv (world : World Key Block) (key : Key) :
    UnusedOutput (reverseWorld world) key ≃ UnusedInput world key where
  toFun input := ⟨input.val, by
    intro e he hk
    exact input.property (flipEntry e) (List.mem_map.mpr ⟨e, he, rfl⟩) hk⟩
  invFun input := ⟨input.val, by
    intro e he hk
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp he
    exact input.property old hold hk⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem unusedInput_nonempty (world : World Key Block) (key : Key) (output : Block)
    (hfresh : FreshOutput world key output) : Nonempty (UnusedInput world key) := by
  letI := unusedOutput_nonempty (reverseWorld world) key output (reverse_fresh_input world key output hfresh)
  exact ⟨unusedInverseEquiv world key (Classical.choice inferInstance)⟩

variable [Fintype Key] [Fintype Block]

/-- Decryption has the forward-answer law for the inverses of the very same
compatible permutations, with every earlier graph entry reversed. -/
theorem decrypt_answers (world : World Key Block) (key : Key) (output : Block) :
    (query world (.decrypt key output)).map Prod.fst =
      (query (reverseWorld world) (.encrypt key output)).map Prod.fst := by
  have h := congrArg (fun p : PMF (Candidates (reverseWorld world)) =>
    p.map (fun family => answer family.val (.encrypt key output)))
    (IntegerSamplingProbability.map_uniform_equiv (inverseCandidates world))
  simpa only [query, PMF.map_comp, Function.comp_def, answer, inverseCandidates] using h

theorem fresh_decrypt_uniform (world : World Key Block) (key : Key) (output : Block)
    (hfresh : FreshOutput world key output) :
    letI : Nonempty (UnusedInput world key) := unusedInput_nonempty world key output hfresh
    (query world (.decrypt key output)).map Prod.fst =
      (PMF.uniformOfFintype (UnusedInput world key)).map Subtype.val := by
  letI : Nonempty (UnusedInput world key) := unusedInput_nonempty world key output hfresh
  letI : Nonempty (UnusedOutput (reverseWorld world) key) :=
    unusedOutput_nonempty (reverseWorld world) key output (reverse_fresh_input world key output hfresh)
  rw [decrypt_answers, fresh_encrypt_uniform (reverseWorld world) key output (reverse_fresh_input world key output hfresh)]
  rw [← IntegerSamplingProbability.map_uniform_equiv (unusedInverseEquiv world key), PMF.map_comp]
  rfl

theorem fresh_decrypt_event_bound (world : World Key Block) (key : Key) (output : Block)
    (hfresh : FreshOutput world key output) (event : Block → Prop) :
    ((query world (.decrypt key output)).map (fun result => decide (event result.1))) true ≤
      (Fintype.card {input : Block // event input} : ℝ≥0∞) /
        (Fintype.card (UnusedInput world key) : ℝ≥0∞) := by
  have h := fresh_encrypt_event_bound (reverseWorld world) key output (reverse_fresh_input world key output hfresh) event
  have he : (query world (.decrypt key output)).map (fun result => decide (event result.1)) =
      (query (reverseWorld world) (.encrypt key output)).map (fun result => decide (event result.1)) := by
    have hmap := congrArg (fun p : PMF Block => p.map (fun value => decide (event value))) (decrypt_answers world key output)
    simpa only [PMF.map_comp, Function.comp_def] using hmap
  rw [← he] at h
  simpa only [Fintype.card_congr (unusedInverseEquiv world key)] using h

end
end SDitH.Proofs.IdealCipherInverse
