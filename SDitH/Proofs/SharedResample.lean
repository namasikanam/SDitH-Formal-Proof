import SDitH.Proofs.CipherResample
import SDitH.Proofs.ChargeExpect
import SDitH.Proofs.TraceSuffix

/-! The shared scheme's resampling laws in the forms the charged hybrids
use. The program-run resampling law holds without the possibility
hypothesis (an impossible history stays impossible along a run, and its
posterior is the identity family on both sides); resampling is
idempotent; an oracle that samples, runs a program on the inner world and
post-processes the result with the outer hash table obeys the
resampling law; sampling before an oracle preserves the law; and the
empty history's posterior is the uniform family, so a key generation
drawing a uniform family yields a resampled world. -/

namespace SDitH.Proofs.SharedResample

open Spec.IdealCipher (Family Entry Matches Candidates)
open Spec.HashCipher (Procedure)
open Spec.HashCipherTrace (Result runFixed mark)
open Spec.SignatureSecurity
open CipherResample GameResample ChargeExpect
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A B : Type*}

/-- Binds agreeing on the support are equal. -/
theorem bind_congr_support (p : PMF A) (f g : A → PMF B) (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha
    rw [ha]
    simp

end Generic

section Cipher

variable {Input Digest Key Block State : Type*} [Fintype Digest] [Nonempty Digest] [Fintype Key] [Fintype Block]

omit [Fintype Key] [Fintype Block] in
/-- A run's cipher history extends the starting history. -/
theorem runFixed_cipher_suffix (procedure : Procedure Input Digest Key Block State) (family : Family Key Block)
    (fuel : Nat) (state : State) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Entry Key Block)) (log : List (Spec.RandomOracleTrace.Entry Input Digest))
    (out : Result Input Digest Key Block State)
    (hout : out ∈ (runFixed procedure family fuel state table hashes ciphers log).support) :
    ∃ new, out.cipherHistory = new ++ ciphers := by
  induction fuel generalizing state table hashes ciphers log out with
  | zero =>
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    exact ⟨[], rfl⟩
  | succ fuel ih =>
    simp only [runFixed] at hout
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    cases action with
    | stop =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst out
      exact ⟨[], rfl⟩
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
      subst heq
      exact ih (next result.1) result.2 ((input, result.1) :: hashes) ciphers _ inner hinner
    | cipher request next =>
      obtain ⟨new, hnew⟩ := ih _ table hashes _ log out hrest
      exact ⟨new ++ [Spec.IdealCipher.entry request (Spec.IdealCipher.answer family request)], by
        rw [hnew, List.append_assoc]; rfl⟩

omit [Fintype Key] [Fintype Block] in
/-- A family matching an extended history matches the history. -/
theorem matches_of_append (family : Family Key Block) (new history : List (Entry Key Block))
    (h : Matches family (new ++ history)) : Matches family history :=
  fun e he => h e (List.mem_append_right new he)

/-- An impossible history's posterior is the identity family. -/
theorem posterior_impossible (history : List (Entry Key Block)) (h : ¬ ∃ family : Family Key Block, Matches family history) :
    posterior history = PMF.pure fun _ => Equiv.refl Block := by
  unfold posterior
  rw [dif_neg h]

/-- The empty history's posterior is the uniform family. -/
theorem posterior_nil :
    posterior ([] : List (Entry Key Block)) = PMF.uniformOfFintype (Family Key Block) := by
  have h1 : posterior ([] : List (Entry Key Block)) =
      posterior (Spec.IdealCipher.empty (Key := Key) (Block := Block)).history := rfl
  rw [h1, posterior_world, ← IntegerSamplingProbability.map_uniform_equiv (IdealCipher.emptyEquiv (Key := Key) (Block := Block))]
  rfl

end Cipher

section Shared

variable {lambda s wit rnd : Nat} {R : Type*}

/-- The program-run resampling law without the possibility hypothesis. -/
theorem runProgram_resample' {A : Type*} (budget : Nat)
    (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd)
      (Spec.DomainSeparation.Bits lambda) (Spec.DomainSeparation.Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (K : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd)
      (Spec.DomainSeparation.Bits lambda) (Spec.DomainSeparation.Bits lambda) A ×
      Spec.SharedScheme.World lambda s wit rnd → PMF R) :
    (resample world).bind (fun w => (Spec.SharedScheme.runProgram budget program w).bind K) =
    (resample world).bind (fun w => (Spec.SharedScheme.runProgram budget program w).bind fun r =>
      (resample r.2).bind fun w' => K (r.1, w')) := by
  by_cases hpos : ∃ family : Family (Spec.DomainSeparation.Bits lambda) (Spec.DomainSeparation.Bits lambda),
      Matches family world.cipherHistory
  · exact runProgram_resample budget program world hpos K
  · have hres : resample world = PMF.pure { world with family := fun _ => Equiv.refl _ } := by
      unfold resample
      rw [posterior_impossible _ hpos, PMF.pure_map]
    rw [hres, PMF.pure_bind, PMF.pure_bind]
    refine bind_congr_support _ _ _ fun r hr => ?_
    obtain ⟨out, hout, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst heq
    obtain ⟨new, hnew⟩ := runFixed_cipher_suffix _ _ _ _ _ _ _ _ out hout
    have himp : ¬ ∃ family : Family (Spec.DomainSeparation.Bits lambda) (Spec.DomainSeparation.Bits lambda),
        Matches family out.cipherHistory := by
      rintro ⟨family, hf⟩
      rw [hnew] at hf
      exact hpos ⟨family, matches_of_append family new _ hf⟩
    show _ = (resample ⟨_, out.hashTable, out.hashHistory, out.cipherHistory, out.trace⟩).bind _
    unfold resample
    rw [posterior_impossible _ himp, PMF.pure_map, PMF.pure_bind]

/-- Resampling is idempotent. -/
theorem resample_idem (world : Spec.SharedScheme.World lambda s wit rnd) :
    (resample world).bind resample = resample world := by
  unfold resample
  simp only [PMF.bind_map, Function.comp_def]
  exact PMF.bind_const _ _

variable {HashInput Digest : Type*}

/-- Sampling before an oracle preserves the resampling law. -/
theorem postLaw_sample {X S : Type*} (res : Spec.SharedScheme.World lambda s wit rnd →
      PMF (Spec.SharedScheme.World lambda s wit rnd)) (sample : PMF X)
    (body : X → World HashInput Digest (Spec.SharedScheme.World lambda s wit rnd) →
      PMF (S × World HashInput Digest (Spec.SharedScheme.World lambda s wit rnd)))
    (h : ∀ x, PostLaw res (body x)) : PostLaw res fun w => sample.bind fun x => body x w := by
  intro world
  conv_lhs => rw [PMF.bind_comm]
  conv_rhs =>
    simp only [PMF.bind_bind]
    rw [PMF.bind_comm]
  congr 1
  funext x
  exact h x world

/-- An oracle that runs a program on the inner world and post-processes
the result with the outer hash table obeys the resampling law. -/
theorem postLaw_run {A S : Type*} (budget : Nat)
    (program : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd)
      (Spec.DomainSeparation.Bits lambda) (Spec.DomainSeparation.Bits lambda) A)
    (post : Spec.HashCipherProgram.Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd)
      (Spec.DomainSeparation.Bits lambda) (Spec.DomainSeparation.Bits lambda) A →
      (HashInput → Option Digest) → PMF (S × (HashInput → Option Digest))) :
    PostLaw (resample (lambda := lambda) (s := s) (wit := wit) (rnd := rnd)) fun w =>
      (Spec.SharedScheme.runProgram budget program w.other).bind fun r =>
        (post r.1 w.hashTable).map fun q => (q.1, ⟨q.2, r.2⟩) := by
  intro world
  unfold resampleW
  simp only [PMF.bind_map, Function.comp_def]
  rw [runProgram_resample' budget program world.other]
  congr 1
  funext o
  simp only [PMF.bind_bind, PMF.map, Function.comp_def, PMF.pure_bind]
  congr 1
  funext r
  rw [PMF.bind_comm]

end Shared

end
end SDitH.Proofs.SharedResample
