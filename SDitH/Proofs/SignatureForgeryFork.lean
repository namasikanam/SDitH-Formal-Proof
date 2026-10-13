import SDitH.Proofs.SignatureQueryProvenance

/-! Quantitative link from actual abstract-game forgery to the defined random
query replay. This experiment still uses the honest signing secret. The result
is not an RSD reduction, and no simulator or extractor is assumed. The query
loss uses the full action budget, including actions other than hash requests. -/

namespace SDitH.Proofs.SignatureForgeryFork

open Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.SignatureQuerySelection
open scoped Classical ENNReal
noncomputable section

theorem boolean_union_bound {A I : Type*} [Fintype I]
    (p : PMF A) (win : A → Bool) (events : I → A → Bool)
    (hcover : ∀ a ∈ p.support, win a = true → ∃ i, events i a = true) :
    (p.map win) true ≤ ∑ i, (p.map (events i)) true :=
  ChallengeMixtures.boolean_union_bound p win events hcover

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

theorem present_winning_mass_le_sum
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) :
    ((experiment (scheme components) adversary fuel).map
      (fun checked => checked.wins && checked.inputWasPresent)) true ≤
      ∑ index : Fin fuel, singleExperiment (scheme components) adversary index.val fuel true := by
  calc
    _ = ((recordedExperiment (scheme components) adversary fuel).map
        (fun out => out.checked.wins && out.checked.inputWasPresent)) true := by
      rw [← SignatureQuerySelection.recorded_experiment_refines, PMF.map_comp]
      rfl
    _ ≤ ∑ index : Fin fuel, ((recordedExperiment (scheme components) adversary fuel).map
        (marked index.val)) true := by
      apply boolean_union_bound
      intro out ho hw
      have hh : out.checked.wins = true ∧ out.checked.inputWasPresent = true := by simpa using hw
      exact SignatureQueryProvenance.present_winner_has_mark components adversary fuel out ho hh.1 hh.2
    _ = _ := by simp_rw [SignatureQuerySelection.selected_experiment_eq]

theorem random_single_mass
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) :
    randomSingleExperiment (scheme components) adversary fuel true =
      ((fuel + 1 : Nat) : ℝ≥0∞)⁻¹ *
        ∑ index : Fin (fuel + 1), singleExperiment (scheme components) adversary index.val (fuel + 1) true := by
  unfold randomSingleExperiment randomCutExperiment
  rw [PMF.bind_bind]
  change ((PMF.uniformOfFintype (Fin (fuel + 1))).bind
    (fun index => singleExperiment (scheme components) adversary index.val (fuel + 1))) true = _
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [Finset.mul_sum]

theorem scaled_random_single_mass
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) :
    ((fuel + 1 : Nat) : ℝ≥0∞) * randomSingleExperiment (scheme components) adversary fuel true =
      ∑ index : Fin (fuel + 1), singleExperiment (scheme components) adversary index.val (fuel + 1) true := by
  rw [random_single_mass, ← mul_assoc, ENNReal.mul_inv_cancel]
  · exact one_mul _
  · exact_mod_cast Nat.succ_ne_zero fuel
  · exact ENNReal.natCast_ne_top _

/-- Overall forgery is bounded by the random fresh-target success probability,
with the proved action-budget selection loss and the fresh-hash guessing term. -/
theorem forgery_to_random_query
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) :
    advantage (scheme components) adversary (fuel + 1) ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) * randomSingleExperiment (scheme components) adversary fuel true +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [scaled_random_single_mass]
  exact (SignatureSecurity.advantage_le_present_plus_guess (scheme components) adversary (fuel + 1)).trans
    (add_le_add (present_winning_mass_le_sum components adversary (fuel + 1)) le_rfl)

/-- Both inequalities concern defined experiments. The intermediate epsilon is
their actual random-query success mass, rather than a supplied security promise. -/
theorem forgery_replay_bounds
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) :
    (advantage (scheme components) adversary (fuel + 1) ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) * randomSingleExperiment (scheme components) adversary fuel true +
        (Fintype.card Digest : ℝ≥0∞)⁻¹) ∧
    ((randomSingleExperiment (scheme components) adversary fuel true) ^ 2 ≤
      randomForkExperiment (scheme components) adversary fuel true +
      randomSingleExperiment (scheme components) adversary fuel true * (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
  exact ⟨forgery_to_random_query components adversary fuel,
    SignatureFork.random_cut_fork_bound (scheme components) adversary
      (randomCutExperiment (scheme components) adversary fuel)⟩

/-- Explicit forgery-to-replay bound for the actual uniform-index algorithm.
The squared action-budget loss is stated as proved, without claiming a sharper
forking theorem, witness extraction, or a reduction without the honest key. -/
theorem forgery_to_fork
    (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (fuel : Nat) :
    (advantage (scheme components) adversary (fuel + 1) - (Fintype.card Digest : ℝ≥0∞)⁻¹) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (randomForkExperiment (scheme components) adversary fuel true + (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
  obtain ⟨hselection, hfork⟩ := forgery_replay_bounds components adversary fuel
  have hsub := tsub_le_iff_right.mpr hselection
  have hsingle : randomSingleExperiment (scheme components) adversary fuel true ≤ 1 :=
    (randomSingleExperiment (scheme components) adversary fuel).coe_le_one true
  calc
    _ ≤ (((fuel + 1 : Nat) : ℝ≥0∞) * randomSingleExperiment (scheme components) adversary fuel true) ^ 2 :=
      ENNReal.pow_le_pow_left hsub
    _ = ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (randomSingleExperiment (scheme components) adversary fuel true) ^ 2 := mul_pow _ _ _
    _ ≤ ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (randomForkExperiment (scheme components) adversary fuel true +
          randomSingleExperiment (scheme components) adversary fuel true * (Fintype.card Digest : ℝ≥0∞)⁻¹) :=
      mul_le_mul_right hfork _
    _ ≤ _ := by
      apply mul_le_mul_right
      apply add_le_add le_rfl
      simpa only [one_mul] using mul_le_mul_left hsingle (Fintype.card Digest : ℝ≥0∞)⁻¹

end
end SDitH.Proofs.SignatureForgeryFork
