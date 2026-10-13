import SDitH.Proofs.HashCipherHash
import SDitH.Proofs.HashCipherPair

namespace SDitH.Proofs.HashCipherSecurity

open Spec.HashCipher
open scoped Classical ENNReal
noncomputable section

variable {Input Digest Key Block State Tag : Type*}
variable [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]

/-- One joint execution, not a sum of bounds for unrelated experiments.
The budget counts all hash and cipher queries, including repeated requests. -/
theorem combined_bound (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity) :
    ((jointExperiment procedure budget initial).map (combinedEvent project companion)) true ≤
      (budget.choose 2 : ℝ≥0∞) *
        ((Fintype.card Digest : ℝ≥0∞)⁻¹ + IdealCipherPairAdaptive.pairCost Block capacity budget) := by
  apply (RandomOracleCollision.boolean_or_mass (jointExperiment procedure budget initial)
    (fun joint => joint.2.hashCollided) (cipherEvent project companion)).trans
  calc
    _ ≤ (budget.choose 2 : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        (budget.choose 2 : ℝ≥0∞) * IdealCipherPairAdaptive.pairCost Block capacity budget :=
      add_le_add (HashCipherHash.joint_hash_bound procedure budget initial)
        (HashCipherPair.experiment_pair_bound procedure budget initial project companion hinvolution hnofix capacity hcapacity)
    _ = _ := (mul_add _ _ _).symm

/-- Transfer to a computed bad event after a caller proves its collision
coverage on actual executions. This lemma is not a supplied binding contract;
source callers must derive the displayed coverage from their computations. -/
theorem event_bound (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State)
    (project : Block → Tag) (companion : Block → Block)
    (hinvolution : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
    (capacity : Nat) (hcapacity : ∀ target, Fintype.card {output : Block // project output = target} ≤ capacity)
    (bad : Result Input Digest Key Block State → Bool)
    (hcover : ∀ joint ∈ (jointExperiment procedure budget initial).support, bad joint.2 = true →
      (∃ pair, Spec.RandomOracleCollision.storedCollision pair (hashView joint.2) = true) ∨
      Spec.IdealCipherPairCollision.Witnessed project companion joint.1 joint.2.cipherHistory) :
    ((experiment procedure budget initial).map bad) true ≤
      (budget.choose 2 : ℝ≥0∞) *
        ((Fintype.card Digest : ℝ≥0∞)⁻¹ + IdealCipherPairAdaptive.pairCost Block capacity budget) := by
  apply le_trans ?_ (combined_bound procedure budget initial project companion hinvolution hnofix capacity hcapacity)
  simp only [experiment, PMF.map_comp, Function.comp_def, PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro joint
  by_cases hs : joint ∈ (jointExperiment procedure budget initial).support
  · by_cases hw : bad joint.2 = true
    · have hh : combinedEvent project companion joint = true := by
        rcases hcover joint hs hw with ⟨pair, hp⟩ | hc
        · simp only [combinedEvent, HashCipherHash.stored_collision_implies_flag procedure budget initial joint hs pair hp, Bool.true_or]
        · simp only [combinedEvent, cipherEvent, hc, decide_true, Bool.or_true]
      simp [hw, hh]
    · simp [hw]
  · have hz : jointExperiment procedure budget initial joint = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hs
    simp [hz]

end
end SDitH.Proofs.HashCipherSecurity
