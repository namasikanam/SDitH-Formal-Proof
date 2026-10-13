import SDitH.Proofs.HashCipher
import SDitH.Proofs.RandomOracleCollisionInvariant

namespace SDitH.Proofs.HashCipherHash

open Spec.HashCipher
open Spec.RandomOracleCollision (Recorded CollisionFree freshHit storedCollision)
open scoped Classical ENNReal
noncomputable section

variable {Input Digest Key Block State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- Cipher queries can adapt the next hash request but do not create a hash
collision themselves. The same birthday bound holds for each fixed family. -/
theorem run_hash_bound (procedure : Procedure Input Digest Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (budget : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block)) :
    ((runFixed procedure family budget state table hashes ciphers).map Result.hashCollided) true ≤
      ((budget * hashes.length + budget.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  induction budget generalizing state table hashes ciphers with
  | zero => simp [runFixed, PMF.pure_map]
  | succ budget ih =>
    simp only [runFixed, PMF.map_bind]
    apply ChallengeMixtures.bind_true_le
    intro action _
    cases action with
    | stop => simp [PMF.pure_map]
    | cipher request next =>
      apply (ih (next (Spec.IdealCipher.answer family request)) table hashes _).trans
      apply mul_le_mul_left
      exact_mod_cast Nat.add_le_add (Nat.mul_le_mul_right hashes.length (Nat.le_succ budget))
        (Nat.choose_le_choose 2 (Nat.le_succ budget))
    | hash input next =>
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, markHash]
      have hrest (result : Digest × (Input → Option Digest)) :
          ((runFixed procedure family budget (next result.1) result.2 ((input, result.1) :: hashes) ciphers).map Result.hashCollided) true ≤
            ((budget * (hashes.length + 1) + budget.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
        ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers
      have hu := RandomOracleCollision.bind_or_bound (Spec.RandomOracle.query table input)
        (fun result => runFixed procedure family budget (next result.1) result.2 ((input, result.1) :: hashes) ciphers)
        (fun result => freshHit table hashes input result.1) Result.hashCollided _ (fun result _ => hrest result)
      apply hu.trans
      calc
        _ ≤ (hashes.length : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
            ((budget * (hashes.length + 1) + budget.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
          add_le_add (RandomOracleCollision.query_hit_bound table hashes input) le_rfl
        _ = _ := by
          rw [← add_mul, ← Nat.cast_add]
          congr 2
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          ring

theorem run_invariants (procedure : Procedure Input Digest Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (budget : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family budget state table hashes ciphers).support)
    (hr : Recorded table hashes) (hc : Spec.IdealCipher.Matches family ciphers) :
    Recorded out.hashTable out.hashHistory ∧ Spec.IdealCipher.Matches family out.cipherHistory ∧
      (CollisionFree table → out.hashCollided = false → CollisionFree out.hashTable) := by
  induction budget generalizing state table hashes ciphers out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨hr, hc, fun h _ => h⟩
  | succ budget ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      rw [PMF.mem_support_pure_iff] at hnext
      subst out
      exact ⟨hr, hc, fun h _ => h⟩
    | cipher request next =>
      exact ih (next (Spec.IdealCipher.answer family request)) table hashes _ out hnext hr
        ((IdealCipher.matches_cons _ _ _ _).mpr ⟨hc, rfl⟩)
    | hash input next =>
      obtain ⟨result, hquery, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      have hs := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers tail ht
        (RandomOracleCollisionInvariant.query_recorded table hashes input result hr hquery) hc
      refine ⟨hs.1, hs.2.1, ?_⟩
      intro hfree hfalse
      have hh : freshHit table hashes input result.1 = false ∧ tail.hashCollided = false :=
        Bool.or_eq_false_iff.mp hfalse
      exact hs.2.2 (RandomOracleCollisionInvariant.query_collisionFree table hashes input result hr hfree hquery hh.1) hh.2

theorem run_lengths (procedure : Procedure Input Digest Key Block State) (family : Spec.IdealCipher.Family Key Block)
    (budget : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family budget state table hashes ciphers).support) :
    out.hashHistory.length + out.cipherHistory.length ≤ hashes.length + ciphers.length + budget := by
  induction budget generalizing state table hashes ciphers out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact Nat.le_refl _
  | succ budget ih =>
    obtain ⟨action, _, hnext⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      rw [PMF.mem_support_pure_iff] at hnext
      subst out
      exact Nat.le_add_right _ _
    | cipher request next =>
      have h := ih (next (Spec.IdealCipher.answer family request)) table hashes _ out hnext
      simp only [List.length_cons] at h
      omega
    | hash input next =>
      obtain ⟨result, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hnext
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst out
      have h := ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers tail ht
      simp only [markHash, List.length_cons] at h ⊢
      omega

variable [Fintype Key] [Fintype Block]

theorem experiment_hash_bound (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State) :
    ((experiment procedure budget initial).map Result.hashCollided) true ≤
      (budget.choose 2 : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp only [experiment, jointExperiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply ChallengeMixtures.bind_true_le
  intro family _
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using
    run_hash_bound procedure family budget initial (fun _ => none) [] []

theorem joint_hash_bound (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State) :
    ((jointExperiment procedure budget initial).map (fun joint => joint.2.hashCollided)) true ≤
      (budget.choose 2 : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simpa only [experiment, PMF.map_comp, Function.comp_def] using experiment_hash_bound procedure budget initial

theorem joint_invariants (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State)
    (joint : Spec.IdealCipher.Family Key Block × Result Input Digest Key Block State)
    (hout : joint ∈ (jointExperiment procedure budget initial).support) :
    Recorded joint.2.hashTable joint.2.hashHistory ∧ Spec.IdealCipher.Matches joint.1 joint.2.cipherHistory ∧
      (joint.2.hashCollided = false → CollisionFree joint.2.hashTable) ∧
      joint.2.hashHistory.length + joint.2.cipherHistory.length ≤ budget := by
  obtain ⟨family, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨out, ho, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst joint
  have h := run_invariants procedure family budget initial (fun _ => none) [] [] out ho
    (by simp [Recorded]) (by simp [Spec.IdealCipher.Matches])
  exact ⟨h.1, h.2.1, h.2.2 (by simp [CollisionFree]), by
    simpa only [List.length_nil, Nat.zero_add] using run_lengths procedure family budget initial (fun _ => none) [] [] out ho⟩

theorem stored_collision_implies_flag (procedure : Procedure Input Digest Key Block State) (budget : Nat) (initial : State)
    (joint : Spec.IdealCipher.Family Key Block × Result Input Digest Key Block State)
    (hout : joint ∈ (jointExperiment procedure budget initial).support)
    (pair : Input × Input) (hwin : storedCollision pair (hashView joint.2) = true) : joint.2.hashCollided = true := by
  obtain ⟨hne, answer, hl, hr⟩ := of_decide_eq_true hwin
  cases he : joint.2.hashCollided with
  | true => rfl
  | false =>
    exact False.elim (hne ((joint_invariants procedure budget initial joint hout).2.2.1 he pair.1 pair.2 answer hl hr))

end
end SDitH.Proofs.HashCipherHash
