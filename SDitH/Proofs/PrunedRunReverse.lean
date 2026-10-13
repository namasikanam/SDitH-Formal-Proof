import SDitH.Proofs.PrunedRun

/-! The reverse agreement: the run from the pruned history is below the run
from the history plus the touching term. The coupling is the same as for the
forward direction; at a pruned key the pruned run's result records the hit,
so its touching term is one. -/

namespace SDitH.Proofs.PrunedRunReverse

open Spec.IdealCipher (Family Entry Matches Candidates World observe answer entry)
open Spec.HashCipher (Procedure)
open Spec.HashCipherTrace (Result runFixed mark)
open Spec.RandomOracleTrap (indicator)
open CipherResample PosteriorPrune HiddenEntries SharedResample ChargeExpect PrunedRun
open scoped Classical ENNReal

noncomputable section

variable {Key Block : Type*} [Fintype Key] [Fintype Block]
variable {Input Digest State : Type*} [Fintype Digest] [Nonempty Digest]

/-- The run from the pruned history is below the run from the history plus
the pruned run's touching term. -/
theorem prune_le_run (K : List Key) (procedure : Procedure Input Digest Key Block State) :
    ∀ (fuel : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
      (H : List (Entry Key Block)) (_hpos : ∃ f : Family Key Block, Matches f H)
      (log : List (Spec.RandomOracleTrace.Entry Input Digest)) (φ : Result Input Digest Key Block State → ℝ≥0∞)
      (_hφ : ∀ out, φ out ≤ 1),
      mean (posterior (pruneAt K H)) (fun f => mean (runFixed procedure f fuel state table hashes (pruneAt K H) log) φ) ≤
      mean (posterior H) (fun f => mean (runFixed procedure f fuel state table hashes H log) fun out =>
        φ (pruneResult K out)) +
      mean (posterior (pruneAt K H)) (fun f => mean (runFixed procedure f fuel state table hashes (pruneAt K H) log)
        fun out => indicator (touches K out)) := by
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
    conv_rhs => arg 1; rw [mean_comm]
    conv_rhs => arg 2; rw [mean_comm]
    rw [← mean_add]
    refine mean_le_mean _ _ _ fun action _ => ?_
    cases action with
    | stop =>
      simp only [mean_pure, mean_const, pruneResult]
      exact le_self_add
    | hash input next =>
      dsimp only
      simp only [mean_bind, mean_map]
      rw [mean_comm]
      conv_rhs => arg 1; rw [mean_comm]
      conv_rhs => arg 2; rw [mean_comm]
      rw [← mean_add]
      refine mean_le_mean _ _ _ fun result _ => ?_
      exact ih (next result.1) result.2 _ H hpos _
        (fun out => φ (mark (Spec.RandomOracleCollision.freshHit table hashes input result.1) out)) (fun out => hφ _)
    | cipher request next =>
      dsimp only
      by_cases hk : keyOf request ∈ K
      · refine (mean_le_const _ _ 1 fun f _ => mean_le_const _ _ 1 fun out _ => hφ _).trans ?_
        refine le_add_self.trans' ?_
        calc (1 : ℝ≥0∞) = mean (posterior (pruneAt K H)) (fun f =>
                mean (runFixed procedure f fuel (next (answer f request)) table hashes
                  (entry request (answer f request) :: pruneAt K H) log) fun _ => 1) := by
              simp only [mean_const]
          _ ≤ _ := mean_le_mean _ _ _ fun f _ => mean_le_mean _ _ _ fun out hout => ?_
        obtain ⟨new, hnew⟩ := runFixed_cipher_suffix procedure f fuel _ table hashes _ log out hout
        rw [touches_of_mem K out (entry request (answer f request))
          (by rw [hnew]; exact List.mem_append_right _ List.mem_cons_self) (by rw [entry_key]; exact hk)]
        exact le_rfl
      · have hfull := congrArg (fun p => mean p fun out => φ (pruneResult K out))
          (posterior_cipher_step ⟨H, hpos⟩ request fun v h f => runFixed procedure f fuel (next v) table hashes h log)
        have hpr := congrArg (fun p => mean p φ)
          (posterior_cipher_step ⟨pruneAt K H, pruneAt_possible K H hpos⟩ request fun v h f =>
            runFixed procedure f fuel (next v) table hashes h log)
        have hbad := congrArg (fun p => mean p fun out => indicator (touches K out))
          (posterior_cipher_step ⟨pruneAt K H, pruneAt_possible K H hpos⟩ request fun v h f =>
            runFixed procedure f fuel (next v) table hashes h log)
        simp only [mean_bind] at hfull hpr hbad
        rw [← hfull, ← hpr, ← hbad]
        have hlaw : (posterior H).map (fun f => answer f request) =
            (posterior (pruneAt K H)).map (fun f => answer f request) :=
          posterior_answer_eq_prune K ⟨H, hpos⟩ request hk
        rw [mean_fun_answer (posterior H) request (fun v => mean (posterior (entry request v :: H)) fun f' =>
            mean (runFixed procedure f' fuel (next v) table hashes (entry request v :: H) log) fun out =>
              φ (pruneResult K out)),
          mean_fun_answer (posterior (pruneAt K H)) request (fun v =>
            mean (posterior (entry request v :: pruneAt K H)) fun f' =>
              mean (runFixed procedure f' fuel (next v) table hashes (entry request v :: pruneAt K H) log) φ),
          mean_fun_answer (posterior (pruneAt K H)) request (fun v =>
            mean (posterior (entry request v :: pruneAt K H)) fun f' =>
              mean (runFixed procedure f' fuel (next v) table hashes (entry request v :: pruneAt K H) log) fun out =>
                indicator (touches K out)),
          hlaw, ← mean_add]
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
end SDitH.Proofs.PrunedRunReverse
