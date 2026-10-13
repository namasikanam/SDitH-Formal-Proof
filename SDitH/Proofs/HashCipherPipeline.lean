import SDitH.Spec.HashCipherPipeline
import SDitH.Proofs.HashCipherHash
import SDitH.Proofs.RandomOraclePipeline

namespace SDitH.Proofs.HashCipherPipeline

open Spec.HashCipher
open Spec.RandomOracleCollision (Recorded CollisionFree storedCollision)
open scoped Classical ENNReal
noncomputable section

variable {Input Digest Key Block A B : Type*}

theorem markHash_false : (markHash false : Result Input Digest Key Block B → _) = id := by
  funext out
  cases out
  rfl

variable [Fintype Digest] [Nonempty Digest]

/-- Composing phases preserves earlier collisions as well as collisions
between a new query and either phase's stored answers. -/
theorem run_hash_bound (first : Procedure Input Digest Key Block A) (q : Nat) (state : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (family : Spec.IdealCipher.Family Key Block) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block)) :
    ((Spec.HashCipherPipeline.runFixed first second k next family q state table hashes ciphers).map Result.hashCollided) true ≤
      (((q + k) * hashes.length + (q + k).choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hlen (start : Result Input Digest Key Block A)
      (hs : start ∈ (runFixed first family q state table hashes ciphers).support) :
      start.hashHistory.length ≤ hashes.length + q := by
    induction q generalizing state table hashes ciphers start with
    | zero =>
      simp only [runFixed, PMF.mem_support_pure_iff] at hs
      subst start
      exact Nat.le_refl _
    | succ q ih =>
      obtain ⟨action, _, ha⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      cases action with
      | stop =>
        rw [PMF.mem_support_pure_iff] at ha
        subst start
        exact Nat.le_add_right _ _
      | cipher request advance =>
        exact (ih (advance (Spec.IdealCipher.answer family request)) table hashes _ start ha).trans (by omega)
      | hash input advance =>
        obtain ⟨result, _, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
        obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
        subst start
        have h := ih (advance result.1) result.2 ((input, result.1) :: hashes) ciphers tail ht
        simp only [markHash, List.length_cons] at h ⊢
        omega
  have hrest (start : Result Input Digest Key Block A)
      (hs : start ∈ (runFixed first family q state table hashes ciphers).support) :
      ((runFixed second family k (next start.state) start.hashTable start.hashHistory start.cipherHistory).map Result.hashCollided) true ≤
        ((k * (hashes.length + q) + k.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    apply (HashCipherHash.run_hash_bound second family k (next start.state) start.hashTable start.hashHistory start.cipherHistory).trans
    apply mul_le_mul_left
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left k (hlen start hs)) (k.choose 2)
  have h := RandomOracleCollision.bind_or_bound (runFixed first family q state table hashes ciphers)
    (fun start => runFixed second family k (next start.state) start.hashTable start.hashHistory start.cipherHistory)
    Result.hashCollided Result.hashCollided _ hrest
  simp only [Spec.HashCipherPipeline.runFixed, PMF.map_bind, PMF.map_comp, Function.comp_def, markHash]
  apply h.trans
  calc
    _ ≤ ((q * hashes.length + q.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        ((k * (hashes.length + q) + k.choose 2 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
      add_le_add (HashCipherHash.run_hash_bound first family q state table hashes ciphers) le_rfl
    _ = _ := by
      rw [← add_mul, ← Nat.cast_add]
      congr 2
      rw [← RandomOraclePipeline.choose_two_add]
      ring

variable [Fintype Key] [Fintype Block]

theorem runPosterior_eq (first : Procedure Input Digest Key Block A) (second : Procedure Input Digest Key Block B)
    (k : Nat) (next : A → B) (q : Nat) (state : A) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (world : Spec.IdealCipher.World Key Block) :
    Spec.HashCipherPipeline.runPosterior first second k next q state table hashes world =
      (PMF.uniformOfFintype (Spec.IdealCipher.Candidates world)).bind (fun family =>
        (Spec.HashCipherPipeline.runFixed first second k next family.val q state table hashes world.history).map
          fun out => (family.val, out)) := by
  induction q generalizing state table hashes world with
  | zero =>
    simp only [Spec.HashCipherPipeline.runPosterior, Spec.HashCipherPipeline.runFixed, runFixed,
      PMF.pure_bind, markHash_false, PMF.map_id, HashCipher.runPosterior_eq]
  | succ q ih =>
    simp only [Spec.HashCipherPipeline.runPosterior, Spec.HashCipherPipeline.runFixed, runFixed,
      PMF.bind_bind, PMF.map_bind]
    rw [PMF.bind_comm]
    congr 1
    funext action
    cases action with
    | stop =>
      simp only [PMF.pure_bind, markHash_false, PMF.map_id, HashCipher.runPosterior_eq]
    | cipher request advance =>
      simp_rw [ih]
      simpa only [Spec.HashCipherPipeline.runFixed, PMF.map_bind] using
        IdealCipherJoint.query_resample world request (fun value history family =>
        (Spec.HashCipherPipeline.runFixed first second k next family q (advance value) table hashes history).map
          fun out => (family, out))
    | hash input advance =>
      simp only [PMF.bind_bind, PMF.bind_map]
      rw [PMF.bind_comm]
      congr 1
      funext result
      simp only [ih, Spec.HashCipherPipeline.runFixed, PMF.map_bind, PMF.map_comp, Function.comp_def,
        markJoint, markHash, Bool.or_assoc]

theorem experiments_eq (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B) :
    Spec.HashCipherPipeline.runPosterior first second k next q initial (fun _ => none) [] Spec.IdealCipher.empty =
      Spec.HashCipherPipeline.jointExperiment first q initial second k next := by
  rw [runPosterior_eq, Spec.HashCipherPipeline.jointExperiment,
    ← IntegerSamplingProbability.map_uniform_equiv (IdealCipher.emptyEquiv (Key := Key) (Block := Block)), PMF.bind_map]
  rfl

theorem hash_bound (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B) :
    ((Spec.HashCipherPipeline.jointExperiment first q initial second k next).map (fun joint => joint.2.hashCollided)) true ≤
      ((q + k).choose 2 : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp only [Spec.HashCipherPipeline.jointExperiment, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply ChallengeMixtures.bind_true_le
  intro family _
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using
    run_hash_bound first q initial second k next family (fun _ => none) [] []

/-- The sequential experiment extends exactly the standalone joint oracle
model. No new or independently sampled oracle is introduced at the boundary. -/
theorem joint_model_extension (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B) :
    Spec.HashCipherPipeline.jointExperiment first q initial second k next =
      (Assumptions.sharedOracleModel first q initial).bind (fun joint =>
        (runFixed second joint.1 k (next joint.2.state) joint.2.hashTable joint.2.hashHistory joint.2.cipherHistory).map
          fun out => (joint.1, markHash joint.2.hashCollided out)) := by
  simp only [Spec.HashCipherPipeline.jointExperiment, Spec.HashCipherPipeline.runFixed,
    Assumptions.sharedOracleModel, jointExperiment, PMF.bind_bind, PMF.bind_map,
    PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem joint_decompose (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (joint : Spec.IdealCipher.Family Key Block × Result Input Digest Key Block B)
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment first q initial second k next).support) :
    ∃ start ∈ (runFixed first joint.1 q initial (fun _ => none) [] []).support,
      ∃ tail ∈ (runFixed second joint.1 k (next start.state) start.hashTable start.hashHistory start.cipherHistory).support,
        joint.2 = markHash start.hashCollided tail := by
  obtain ⟨family, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨out, ho, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst joint
  obtain ⟨start, hs, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
  obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp htail
  exact ⟨start, hs, tail, ht, he.symm⟩

theorem invariants (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (joint : Spec.IdealCipher.Family Key Block × Result Input Digest Key Block B)
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment first q initial second k next).support) :
    Recorded joint.2.hashTable joint.2.hashHistory ∧ Spec.IdealCipher.Matches joint.1 joint.2.cipherHistory ∧
      (joint.2.hashCollided = false → CollisionFree joint.2.hashTable) ∧
      joint.2.hashHistory.length + joint.2.cipherHistory.length ≤ q + k := by
  obtain ⟨family, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨out, ho, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst joint
  obtain ⟨start, hs, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp ho
  obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp htail
  subst out
  have hf := HashCipherHash.run_invariants first family q initial (fun _ => none) [] [] start hs
    (by simp [Recorded]) (by simp [Spec.IdealCipher.Matches])
  have hsnd := HashCipherHash.run_invariants second family k (next start.state) start.hashTable start.hashHistory start.cipherHistory tail ht hf.1 hf.2.1
  refine ⟨hsnd.1, hsnd.2.1, ?_, ?_⟩
  · intro hflag
    have hh : start.hashCollided = false ∧ tail.hashCollided = false := Bool.or_eq_false_iff.mp hflag
    exact hsnd.2.2 (hf.2.2 (by simp [CollisionFree]) hh.1) hh.2
  · have hfirst := HashCipherHash.run_lengths first family q initial (fun _ => none) [] [] start hs
    have hsecond := HashCipherHash.run_lengths second family k (next start.state) start.hashTable start.hashHistory start.cipherHistory tail ht
    simp only [List.length_nil, Nat.zero_add] at hfirst
    change tail.hashHistory.length + tail.cipherHistory.length ≤ q + k
    omega

theorem stored_collision_implies_flag (first : Procedure Input Digest Key Block A) (q : Nat) (initial : A)
    (second : Procedure Input Digest Key Block B) (k : Nat) (next : A → B)
    (joint : Spec.IdealCipher.Family Key Block × Result Input Digest Key Block B)
    (hout : joint ∈ (Spec.HashCipherPipeline.jointExperiment first q initial second k next).support)
    (pair : Input × Input) (hwin : storedCollision pair (hashView joint.2) = true) : joint.2.hashCollided = true := by
  obtain ⟨hne, answer, hl, hr⟩ := of_decide_eq_true hwin
  cases he : joint.2.hashCollided with
  | true => rfl
  | false =>
    exact False.elim (hne ((invariants first q initial second k next joint hout).2.2.1 he pair.1 pair.2 answer hl hr))

end
end SDitH.Proofs.HashCipherPipeline
