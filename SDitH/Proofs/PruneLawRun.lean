import SDitH.Proofs.GamePrune

/-! Prune laws, growth and consistency for program-shaped oracles. An oracle
that runs a program on the shared world and post-processes from the outer
hash table obeys the prune law by the shared lift, grows by the run's
history extension, and keeps consistency by the run's matching; sampling
before an oracle and a pure answer preserve all three. These are the generic
forms the candidate scheme's oracles instantiate. -/

namespace SDitH.Proofs.PruneLawRun

open Spec.SignatureSecurity
open Spec.IdealCipher (Family Matches)
open Spec.HashCipherTrace (Result runFixed)
open Spec.RandomOracleTrap (indicator)
open Spec.DomainSeparation (Bits)
open GameResample ChargeExpect CipherResample SharedPrune HiddenEntries GamePrune SharedResample
open scoped Classical ENNReal

noncomputable section

variable {HashInput Digest : Type*}
variable {lambda s wit rnd : Nat}

/-- A pruned shared world touches nothing. -/
theorem touchesW_pruneShared (K : List (Bits lambda)) (o : Spec.SharedScheme.World lambda s wit rnd) :
    touchesW K (pruneShared K o) = false := by
  simp only [touchesW, pruneShared, decide_eq_false_iff_not, not_exists, not_and]
  intro e he
  exact (mem_pruneAt.mp he).2

/-- A run's result history is matched by the family that matches its start. -/
theorem runFixed_matches {Input Key Block State : Type*} [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]
    (procedure : Spec.HashCipher.Procedure Input Digest Key Block State)
    (family : Family Key Block) (fuel : Nat) (state : State) (table : Input → Option Digest)
    (hashes : List (Input × Digest)) (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (log : List (Spec.RandomOracleTrace.Entry Input Digest)) (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support)
    (hm : Matches family ciphers) : Matches family out.cipherHistory := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    exact hm
  | succ fuel ih =>
    simp only [runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst hrest
      exact hm
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      exact ih _ _ _ _ _ inner hinner hm
    | cipher request next =>
      refine ih _ _ _ _ _ out hrest ?_
      exact (IdealCipher.matches_cons family ciphers request _).mpr ⟨hm, rfl⟩

section Run

variable {A S : Type*} (K : List (Bits lambda)) (budget : Nat)
  (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
    (Bits lambda) A)
  (post : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
    (Bits lambda) A → (HashInput → Option Digest) → PMF (S × (HashInput → Option Digest)))

/-- The program-shaped oracle. -/
def runOracle (w : GW HashInput Digest lambda s wit rnd) : PMF (S × GW HashInput Digest lambda s wit rnd) :=
  (Spec.SharedScheme.runProgram budget program w.other).bind fun r =>
    (post r.1 w.hashTable).map fun q => (q.1, ⟨q.2, r.2⟩)

/-- A program-shaped oracle grows. -/
theorem grows_run : Grows (runOracle (HashInput := HashInput) (Digest := Digest) budget program post) := by
  intro w r hr
  simp only [runOracle, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hr
  obtain ⟨p, hp, q, -, rfl⟩ := hr
  simp only [Spec.SharedScheme.runProgram, PMF.mem_support_map_iff] at hp
  obtain ⟨out, hout, rfl⟩ := hp
  exact runFixed_cipher_suffix _ _ _ _ _ _ _ _ out hout

/-- A program-shaped oracle keeps consistency. -/
theorem keeps_run : Keeps (runOracle (HashInput := HashInput) (Digest := Digest) budget program post) := by
  intro w r hw hr
  simp only [runOracle, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hr
  obtain ⟨p, hp, q, -, rfl⟩ := hr
  simp only [Spec.SharedScheme.runProgram, PMF.mem_support_map_iff] at hp
  obtain ⟨out, hout, rfl⟩ := hp
  exact runFixed_matches _ _ _ _ _ _ _ _ out hout hw

/-- A program-shaped oracle obeys the prune law. -/
theorem pruneLaw_run : PruneLaw K (runOracle (HashInput := HashInput) (Digest := Digest) budget program post) := by
  intro world hposs Ψ hΨ hle
  simp only [runOracle, resampleW, mean_map, mean_bind]
  set ψ : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda)
      (Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd → ℝ≥0∞ := fun p =>
    mean (post p.1 world.hashTable) fun q => Ψ (q.1, ⟨q.2, p.2⟩) with hψ
  have hψfree : FamilyFree fun p => if touchesW K p.2 then 0 else ψ p := by
    intro a o f
    show (if touchesW K o then 0 else mean (post a world.hashTable) fun q => Ψ (q.1, setFamily ⟨q.2, o⟩ f)) = _
    have hΨ' := hΨ
    unfold FamilyFreeG at hΨ'
    simp only [hΨ', hψ]
  have hψle : ∀ p, (if touchesW K p.2 then 0 else ψ p) ≤ 1 := by
    intro p
    split
    · exact zero_le _
    · exact mean_le_const _ _ 1 fun q _ => hle _
  have h := runProgram_le_prune K budget program world.other hposs _ hψfree hψle
  refine le_of_eq_of_le ?_ (h.trans (le_of_eq ?_))
  · refine congrArg _ (funext fun o => congrArg _ (funext fun r => ?_))
    simp only [touchesW_pruneShared, Bool.false_eq_true, ↓reduceIte, hψ]
    rfl
  · refine congrArg _ (funext fun o => congrArg _ (funext fun r => ?_))
    by_cases ht : touchesW K r.2 = true
    · simp only [ht, ↓reduceIte, RandomOracleTrap.indicator_true, zero_add, touchesG, mean_const]
    · have ht' : touchesW K r.2 = false := by simpa using ht
      simp only [ht', Bool.false_eq_true, ↓reduceIte, RandomOracleTrap.indicator_false, add_zero, touchesG, hψ]
      rfl

end Run

section Sample

variable {X S : Type*} (K : List (Bits lambda)) (sample : PMF X)
  (body : X → GW HashInput Digest lambda s wit rnd → PMF (S × GW HashInput Digest lambda s wit rnd))

/-- Sampling before an oracle preserves growth. -/
theorem grows_sample (h : ∀ x, Grows (body x)) : Grows fun w => sample.bind fun x => body x w := by
  intro w r hr
  obtain ⟨x, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  exact h x w r hr

/-- Sampling before an oracle preserves consistency keeping. -/
theorem keeps_sample (h : ∀ x, Keeps (body x)) : Keeps fun w => sample.bind fun x => body x w := by
  intro w r hw hr
  obtain ⟨x, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  exact h x w r hw hr

/-- Sampling before an oracle preserves the prune law. -/
theorem pruneLaw_sample (h : ∀ x, PruneLaw K (body x)) : PruneLaw K fun w => sample.bind fun x => body x w := by
  intro world hposs Ψ hΨ hle
  simp only [mean_bind]
  rw [mean_comm]
  conv_rhs => rw [mean_comm]
  exact mean_le_mean _ _ _ fun x _ => h x world hposs Ψ hΨ hle

end Sample

section Pure

variable {S : Type*} (K : List (Bits lambda)) (a : S)

/-- A pure answer grows. -/
theorem grows_pure : Grows fun w : GW HashInput Digest lambda s wit rnd => PMF.pure (a, w) := by
  intro w r hr
  simp only [PMF.mem_support_pure_iff] at hr
  subst hr
  exact ⟨[], rfl⟩

/-- A pure answer keeps consistency. -/
theorem keeps_pure : Keeps fun w : GW HashInput Digest lambda s wit rnd => PMF.pure (a, w) := by
  intro w r hw hr
  simp only [PMF.mem_support_pure_iff] at hr
  subst hr
  exact hw

/-- A pure answer obeys the prune law. -/
theorem pruneLaw_pure : PruneLaw K fun w : GW HashInput Digest lambda s wit rnd => PMF.pure (a, w) := by
  intro world _ Ψ hΨ _
  simp only [mean_pure]
  rw [mean_resampleW_const (fun w => Ψ (a, pruneW K w)) (fun w f => hΨ a (pruneW K w) f),
    mean_resampleW_const (fun w => if touchesG K w then 1 else Ψ (a, w)) (fun w f => by
      show (if touchesG K w then 1 else Ψ (a, setFamily w f)) = _
      rw [hΨ])]
  have ht : touchesG K (pruneW K world) = false := touchesW_pruneShared K world.other
  simp only [ht, Bool.false_eq_true, ↓reduceIte, le_refl]

end Pure

end
end SDitH.Proofs.PruneLawRun
