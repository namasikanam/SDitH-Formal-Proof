import SDitH.Proofs.TraceLength
import SDitH.Proofs.SimulationGapGen

/-! The shared trace's growth along the game's services. The honest and
simulated signings run the commitment program, so they add at most the
commitment budget to the shared trace; the public oracle runs one query,
so it adds at most one entry; the commitment budget is at least one. -/

namespace SDitH.Proofs.TraceGrowth

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.HashCipherTrace
open Spec.PIOPArithmetic (selectorCount)
open SignStep TraceLength SimulationGapInv SimulationGapGen CommitSplitRun
open scoped Classical

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- A shared run's world has at most the budget more trace entries. -/
theorem runProgram_trace_le {A : Type*} (budget : Nat)
    (program : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
      (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) A)
    (world : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (result)
    (hr : result ∈ (runProgram budget program world).support) :
    result.2.trace.length ≤ world.trace.length + budget := by
  obtain ⟨out, hout, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  exact runFixed_trace_length_le procedure world.family budget program world.hashTable world.hashHistory
    world.cipherHistory world.trace out hout

/-- The honest signing adds at most the commitment budget to the shared
trace. -/
theorem honest_sign_trace_le (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (r)
    (hr : r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message
      world).support) :
    r.2.other.trace.length ≤ world.other.trace.length + commitBudget tau kappa := by
  rcases sk with ⟨pk', witness⟩
  rw [honest_sign_eq'] at hr
  obtain ⟨salt, _, h1⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, h2⟩ := (PMF.mem_support_bind_iff _ _ _).mp h1
  obtain ⟨res, hres, h3⟩ := (PMF.mem_support_bind_iff _ _ _).mp h2
  obtain ⟨hashResult, _, h4⟩ := (PMF.mem_support_bind_iff _ _ _).mp h3
  obtain ⟨opened, hop, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp h4
  subst heq
  simp only [Spec.CandidateScheme.openSigning, PMF.mem_support_pure_iff] at hop
  subst hop
  have hpre : (preparedOf S salt res).2.2 = res.2 := by
    unfold preparedOf
    cases res.1 <;> rfl
  dsimp only
  rw [hpre]
  exact runProgram_trace_le _ _ world.other res hres

/-- The simulated signing adds at most the commitment budget to the shared
trace. -/
theorem simulatedSign_trace_le (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (r) (hr : r ∈ (simulatedSign S publicKey message world).support) :
    r.2.other.trace.length ≤ world.other.trace.length + commitBudget tau kappa := by
  obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
  obtain ⟨fake, _, hfake⟩ := (PMF.mem_support_bind_iff _ _ _).mp hroot
  obtain ⟨digest, _, hdigest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfake
  obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hdigest
  have hlen := runProgram_trace_le _ _ world.other run hrun
  rw [← hres]
  dsimp only
  split <;> (try split) <;> (try split) <;> exact hlen

/-- The public oracle adds at most one entry to the shared trace. -/
theorem publicOracle_trace_le (query : Query lambda)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (r) (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).publicOracle query world).support) :
    r.2.other.trace.length ≤ world.other.trace.length + 1 := by
  obtain ⟨result, hresult, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  dsimp only
  cases query with
  | hash input =>
    obtain ⟨run, hrun, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    exact runProgram_trace_le 1 _ world.other run hrun
  | mask input =>
    obtain ⟨run, hrun, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    exact runProgram_trace_le 1 _ world.other run hrun
  | cipher request =>
    obtain ⟨run, hrun, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
    exact runProgram_trace_le 1 _ world.other run hrun

omit [NeZero tau] in
/-- The commitment budget is at least one. -/
theorem one_le_commitBudget : 1 ≤ commitBudget tau kappa := by
  rw [commitBudget_eq]
  omega

end
end SDitH.Proofs.TraceGrowth
