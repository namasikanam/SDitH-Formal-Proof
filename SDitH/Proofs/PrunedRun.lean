import SDitH.Proofs.PosteriorPrune
import SDitH.Proofs.SharedResample
import SDitH.Proofs.ChargeExpect

/-! A run agrees with its run from the pruned history until a query hits
the pruned keys. Against the posterior family, a cipher step is the answer
followed by a fresh posterior draw at the extended history; at a key
outside the pruned keys the answer has the same law under the history and
under its pruned history, and the extended histories prune to each other;
at a key among them the pruned run's result records the hit. So the mean of
a bounded function of the pruned result under the run from the history is
at most its mean under the run from the pruned history plus the pruned
run's probability of touching the keys. -/

namespace SDitH.Proofs.PrunedRun

open Spec.IdealCipher (Family Entry Matches Candidates World observe answer entry)
open Spec.HashCipher (Procedure)
open Spec.HashCipherTrace (Result runFixed mark)
open Spec.RandomOracleTrap (indicator)
open CipherResample PosteriorPrune HiddenEntries SharedResample ChargeExpect
open scoped Classical ENNReal

noncomputable section

variable {Key Block : Type*} [Fintype Key] [Fintype Block]

/-- Against the posterior family, a cipher step is the answer followed by a
fresh posterior draw at the extended history. -/
theorem posterior_cipher_step {R : Type*} (world : World Key Block) (request : Spec.IdealCipher.Query Key Block)
    (next : Block → List (Entry Key Block) → Family Key Block → PMF R) :
    (posterior world.history).bind (fun f => (posterior (entry request (answer f request) :: world.history)).bind fun f' =>
      next (answer f request) (entry request (answer f request) :: world.history) f') =
    (posterior world.history).bind fun f =>
      next (answer f request) (entry request (answer f request) :: world.history) f := by
  rw [posterior_world, PMF.bind_map, PMF.bind_map]
  have h := IdealCipher.posterior_step world request next
  simp only [Function.comp_def] at h ⊢
  rw [← h]
  congr 1
  funext sample
  show (posterior (observe world request (answer sample.val request) ⟨sample.val, sample.property, rfl⟩).history).bind _ = _
  rw [posterior_world, PMF.bind_map]
  rfl

/-- A family in the posterior's support matches the history. -/
theorem matches_of_mem_posterior (H : List (Entry Key Block)) (hpos : ∃ f : Family Key Block, Matches f H)
    (f : Family Key Block) (hf : f ∈ (posterior H).support) : Matches f H := by
  unfold posterior at hf
  rw [dif_pos hpos, PMF.support_map] at hf
  obtain ⟨c, _, rfl⟩ := hf
  exact c.property

omit [Fintype Key] [Fintype Block] in
/-- The key of a recorded entry is the request's key. -/
theorem entry_key (request : Spec.IdealCipher.Query Key Block) (value : Block) :
    (entry request value).key = keyOf request := by
  cases request <;> rfl

omit [Fintype Key] [Fintype Block] in
theorem pruneAt_cons_of_not_mem (K : List Key) (e : Entry Key Block) (H : List (Entry Key Block)) (he : e.key ∉ K) :
    pruneAt K (e :: H) = e :: pruneAt K H := by
  simp [pruneAt, he]

omit [Fintype Key] [Fintype Block] in
theorem pruneAt_cons_of_mem (K : List Key) (e : Entry Key Block) (H : List (Entry Key Block)) (he : e.key ∈ K) :
    pruneAt K (e :: H) = pruneAt K H := by
  simp [pruneAt, he]

variable {Input Digest State : Type*} [Fintype Digest] [Nonempty Digest]

/-- A result with its cipher history pruned at the keys. -/
def pruneResult (K : List Key) (out : Result Input Digest Key Block State) : Result Input Digest Key Block State :=
  { out with cipherHistory := pruneAt K out.cipherHistory }

/-- The result's cipher history has an entry at the keys. -/
def touches (K : List Key) (out : Result Input Digest Key Block State) : Bool :=
  decide (∃ e ∈ out.cipherHistory, e.key ∈ K)

omit [Fintype Key] [Fintype Block] [Fintype Digest] [Nonempty Digest] in
theorem touches_of_mem (K : List Key) (out : Result Input Digest Key Block State) (e : Entry Key Block)
    (he : e ∈ out.cipherHistory) (hk : e.key ∈ K) : touches K out = true := by
  simp only [touches, decide_eq_true_eq]
  exact ⟨e, he, hk⟩

omit [Fintype Key] [Fintype Block] in
/-- A mean over the family of a function of the answer is the mean over the
answer's law. -/
theorem mean_fun_answer (p : PMF (Family Key Block)) (request : Spec.IdealCipher.Query Key Block) (G : Block → ℝ≥0∞) :
    mean p (fun f => G (answer f request)) = mean (p.map fun f => answer f request) G :=
  (mean_map _ _ _).symm

/-- The run from a history agrees with the run from its pruned history until
a query hits the pruned keys: for a function bounded by one, the mean of the
function of the pruned result under the run from the history is at most the
mean of the function plus the touching indicator under the run from the
pruned history. -/
theorem run_le_prune (K : List Key) (procedure : Procedure Input Digest Key Block State) :
    ∀ (fuel : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
      (H : List (Entry Key Block)) (_hpos : ∃ f : Family Key Block, Matches f H)
      (log : List (Spec.RandomOracleTrace.Entry Input Digest)) (φ : Result Input Digest Key Block State → ℝ≥0∞)
      (_hφ : ∀ out, φ out ≤ 1),
      mean (posterior H) (fun f => mean (runFixed procedure f fuel state table hashes H log) fun out =>
        φ (pruneResult K out)) ≤
      mean (posterior (pruneAt K H)) (fun f => mean (runFixed procedure f fuel state table hashes (pruneAt K H) log)
        fun out => φ out + indicator (touches K out)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro state table hashes H _ log φ _
    simp only [runFixed, mean_pure, mean_const, pruneResult]
    exact le_self_add
  | succ fuel ih =>
    intro state table hashes H hpos log φ hφ
    simp only [runFixed, mean_bind]
    rw [mean_comm]
    conv_rhs => rw [mean_comm]
    refine mean_le_mean _ _ _ fun action _ => ?_
    cases action with
    | stop =>
      simp only [mean_pure, mean_const, pruneResult]
      exact le_self_add
    | hash input next =>
      dsimp only
      simp only [mean_bind, mean_map]
      rw [mean_comm]
      conv_rhs => rw [mean_comm]
      refine mean_le_mean _ _ _ fun result _ => ?_
      exact ih (next result.1) result.2 _ H hpos _
        (fun out => φ (mark (Spec.RandomOracleCollision.freshHit table hashes input result.1) out)) (fun out => hφ _)
    | cipher request next =>
      dsimp only
      by_cases hk : keyOf request ∈ K
      · refine (mean_le_const _ _ 1 fun f _ => mean_le_const _ _ 1 fun out _ => hφ _).trans ?_
        calc (1 : ℝ≥0∞) = mean (posterior (pruneAt K H)) (fun f =>
                mean (runFixed procedure f fuel (next (answer f request)) table hashes
                  (entry request (answer f request) :: pruneAt K H) log) fun _ => 1) := by
              simp only [mean_const]
          _ ≤ _ := mean_le_mean _ _ _ fun f _ => mean_le_mean _ _ _ fun out hout => ?_
        obtain ⟨new, hnew⟩ := runFixed_cipher_suffix procedure f fuel _ table hashes _ log out hout
        rw [touches_of_mem K out (entry request (answer f request))
          (by rw [hnew]; exact List.mem_append_right _ List.mem_cons_self) (by rw [entry_key]; exact hk)]
        exact le_add_self
      · have hfull := congrArg (fun p => mean p fun out => φ (pruneResult K out))
          (posterior_cipher_step ⟨H, hpos⟩ request fun v h f => runFixed procedure f fuel (next v) table hashes h log)
        have hpr := congrArg (fun p => mean p fun out => φ out + indicator (touches K out))
          (posterior_cipher_step ⟨pruneAt K H, pruneAt_possible K H hpos⟩ request fun v h f =>
            runFixed procedure f fuel (next v) table hashes h log)
        simp only [mean_bind] at hfull hpr
        rw [← hfull, ← hpr]
        have hlaw : (posterior H).map (fun f => answer f request) =
            (posterior (pruneAt K H)).map (fun f => answer f request) :=
          posterior_answer_eq_prune K ⟨H, hpos⟩ request hk
        rw [mean_fun_answer (posterior H) request (fun v => mean (posterior (entry request v :: H)) fun f' =>
            mean (runFixed procedure f' fuel (next v) table hashes (entry request v :: H) log) fun out =>
              φ (pruneResult K out)),
          mean_fun_answer (posterior (pruneAt K H)) request (fun v =>
            mean (posterior (entry request v :: pruneAt K H)) fun f' =>
              mean (runFixed procedure f' fuel (next v) table hashes (entry request v :: pruneAt K H) log) fun out =>
                φ out + indicator (touches K out)),
          hlaw]
        refine mean_le_mean _ _ _ fun v hv => ?_
        have hv' : v ∈ ((posterior H).map fun f => answer f request).support := by
          rw [hlaw]
          exact hv
        rw [PMF.support_map] at hv'
        obtain ⟨f, hf, hfv⟩ := hv'
        have hpos' : ∃ g : Family Key Block, Matches g (entry request v :: H) :=
          (observe ⟨H, hpos⟩ request v ⟨f, matches_of_mem_posterior H hpos f hf, hfv⟩).possible
        have := ih (next v) table hashes (entry request v :: H) hpos' log φ hφ
        rw [pruneAt_cons_of_not_mem K _ H (by rw [entry_key]; exact hk)] at this
        exact this

end
end SDitH.Proofs.PrunedRun
