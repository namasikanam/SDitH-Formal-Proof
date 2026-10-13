import SDitH.Spec.SignatureSecurity
import SDitH.Proofs.ChallengeMixtures
import SDitH.Spec.DomainSeparation

/-! First quantitative step for the abstract §5.3 chosen-message game:
acceptance at an absent final hash input has probability at most 1/|Digest|.
This is proved from lazy sampling, for the actual adaptive experiment. It is
not a reduction from the table-present case to knowledge extraction or RSD. -/

namespace SDitH.Proofs.SignatureSecurity

open Spec.SignatureSecurity
open scoped Classical ENNReal
noncomputable section

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

theorem fresh_hash_guess (table : HashInput → Option Digest) (input : HashInput)
    (target : Digest) (hfresh : table input = none) :
    ((Spec.RandomOracle.query table input).map (fun result => decide (result.1 = target))) true =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [Spec.RandomOracle.query, hfresh, PMF.map_comp]
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hs : ((fun answer : Digest => decide (answer = target)) ⁻¹' {true}) = {target} := by
    ext answer
    simp
  change (PMF.uniformOfFintype Digest).toOuterMeasure
    ((fun answer : Digest => decide (answer = target)) ⁻¹' {true}) = _
  rw [hs, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]

theorem finalize_unqueried_bound
    (terminal : Terminal Message Signature HashInput Digest Other Query) :
    ((finalize terminal).map (fun checked => checked.wins && !checked.inputWasPresent)) true ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  cases terminal with
  | exhausted trace => simp [finalize, PMF.pure_map]
  | aborted trace => simp [finalize, PMF.pure_map]
  | rejected trace => simp [finalize, PMF.pure_map]
  | attempt a =>
    cases he : a.world.hashTable a.input with
    | some answer => simp [finalize, Spec.RandomOracle.query, he, PMF.pure_map]
    | none =>
      by_cases hfresh : a.message ∉ a.trace.signingRequests
      · have h := fresh_hash_guess a.world.hashTable a.input a.target he
        simpa [finalize, PMF.map_comp, Function.comp_def, he, hfresh] using h.le
      · simp [finalize, PMF.map_comp, Function.comp_def, hfresh]

/-- Arbitrary adaptive prefixes are allowed. Freshness is tested against the
actual table after the entire prefix, including preparation for verification. -/
theorem terminal_law_unqueried_bound
    (terminals : PMF (Terminal Message Signature HashInput Digest Other Query)) :
    ((terminals.bind finalize).map (fun checked => checked.wins && !checked.inputWasPresent)) true ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [PMF.map_bind]
  apply ChallengeMixtures.bind_true_le
  intro terminal _
  exact finalize_unqueried_bound terminal

theorem finalize_winning_attempt
    (terminal : Terminal Message Signature HashInput Digest Other Query)
    (checked : Checked Message Signature HashInput Digest Other Query)
    (hc : checked ∈ (finalize terminal).support) (hw : checked.wins = true) :
    ∃ a, terminal = .attempt a ∧ checked.terminal = .attempt a ∧
      a.message ∉ a.trace.signingRequests ∧
      checked.inputWasPresent = (a.world.hashTable a.input).isSome := by
  cases terminal with
  | exhausted trace =>
    simp only [finalize, PMF.mem_support_pure_iff] at hc
    subst checked
    contradiction
  | aborted trace =>
    simp only [finalize, PMF.mem_support_pure_iff] at hc
    subst checked
    contradiction
  | rejected trace =>
    simp only [finalize, PMF.mem_support_pure_iff] at hc
    subst checked
    contradiction
  | attempt a =>
    obtain ⟨result, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
    subst checked
    have hf : a.message ∉ a.trace.signingRequests ∧ result.1 = a.target := of_decide_eq_true hw
    exact ⟨a, rfl, rfl, hf.1, rfl⟩

theorem euf_unqueried_bound
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) :
    ((experiment scheme adversary fuel).map
      (fun checked => checked.wins && !checked.inputWasPresent)) true ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
  terminal_law_unqueried_bound (terminalLaw scheme adversary fuel)

omit [Fintype Digest] [Nonempty Digest] in
theorem winning_partition
    (p : PMF (Checked Message Signature HashInput Digest Other Query)) :
    (p.map Checked.wins) true =
      (p.map (fun checked => checked.wins && checked.inputWasPresent)) true +
      (p.map (fun checked => checked.wins && !checked.inputWasPresent)) true := by
  simp only [PMF.map_apply]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro checked
  cases checked.wins <;> cases checked.inputWasPresent <;> simp

/-- A first signature-game reduction: the total forgery probability is at
most the table-present winning event plus the guessing term. Bounding that
remaining event by extraction/SD hardness is still required. -/
theorem advantage_le_present_plus_guess
    (scheme : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
    (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
    (fuel : Nat) :
    advantage scheme adversary fuel ≤
      ((experiment scheme adversary fuel).map
        (fun checked => checked.wins && checked.inputWasPresent)) true +
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [advantage, winning_partition]
  exact add_le_add le_rfl (euf_unqueried_bound scheme adversary fuel)

/-- For SDitH's 2*lambda-bit final hash, the bound is exactly 2^(-2*lambda).
This is a ROM lemma, not an assertion about concrete deterministic SHAKE. -/
theorem sdith_digest_card (lambda : Nat) :
    (Fintype.card (Spec.DomainSeparation.Bits (2 * lambda)) : ℝ≥0∞)⁻¹ =
      ((2 : ℝ≥0∞) ^ (2 * lambda))⁻¹ := by
  simp [Spec.DomainSeparation.Bits]

end
end SDitH.Proofs.SignatureSecurity
