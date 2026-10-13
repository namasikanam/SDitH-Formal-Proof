import SDitH.Proofs.DigestFirstBody

/-! The digest-first honest signing against the fixed-witness simulated
signing. Under payload consistency and a solution witness, at every
salt, root, run result and digest with a returned retry, the digest-first
honest body equals the simulated body (same hash input, same opening,
same programmed table); so the digest-first honest signing is within the
retry-failure event's probability of the fixed-witness simulated
signing. -/

namespace SDitH.Proofs.DigestFirstVsSimulated

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.HashCipherEvaluation Spec.SlopeConsistencyGame Spec.BLCRetry Spec.CandidateBAVC
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open SignStep SignCompare SimulatedWith DigestFirstBody CommitLinesEvent PrefixFromHead
open scoped Classical ENNReal

noncomputable section

section Generic

variable {A B C : Type*}

/-- Two continuations within a bound-shaped event: the binds are within the
event's bind. -/
theorem bind_le_bind_add_bind (p : PMF A) (f g : A → PMF B) (e : A → PMF Bool) (b : B)
    (h : ∀ a ∈ p.support, f a b ≤ g a b + (e a) true) :
    (p.bind f) b ≤ (p.bind g) b + (p.bind e) true := by
  have hc := bind_le_bind_add_cost p f g (fun a => (e a) true) b h
  simpa only [PMF.bind_apply] using hc

/-- A map inside a bind commutes with the outer bind. -/
theorem bind_map_comm (p : PMF A) (q : PMF B) (f : A → B → C) :
    (p.bind fun a => q.map (f a)) = q.bind fun b => p.map fun a => f a b := by
  simp only [← PMF.bind_pure_comp, Function.comp_def]
  exact PMF.bind_comm p q fun a b => PMF.pure (f a b)

end Generic

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The retry-failure event over the honest preparation and a uniform
digest. -/
def retryEvent (publicKey : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : PMF Bool :=
  (prepareSigning S publicKey witness message world.other).bind fun prepared =>
    (PMF.uniformOfFintype (Digest lambda)).map fun digest => retryFails S prepared.2.1 digest

/-- The digest-first honest signing is within the retry-failure event's
probability of the fixed-witness simulated signing. -/
theorem digestFirst_le_simulatedWith (hpc : PayloadConsistent S) (publicKey : List Bool)
    (witness : Fin (selectorCount widths * w) → ZMod 2) (hsol : IsSolution S witness) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (b : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    (digestFirstSign S publicKey witness message world) b ≤
      (simulatedSignWith S publicKey witness message world) b + (retryEvent S publicKey witness message world) true := by
  unfold digestFirstSign simulatedSignWith retryEvent
  rw [prepareSigning_eq]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine bind_le_bind_add_bind _ _ _ _ b (fun salt _ => ?_)
  refine bind_le_bind_add_bind _ _ _ _ b (fun root _ => ?_)
  rw [bind_map_comm]
  refine bind_le_bind_add_bind _ _ _ _ b (fun result hres => ?_)
  rw [← PMF.bind_pure_comp]
  refine bind_le_bind_add_event _ _ _ (fun digest => retryFails S (preparedOf S salt result).2.1 digest)
    (fun digest _ hfail => ?_) b
  obtain ⟨ctr, opening, hobs⟩ := returned_of_not_retryFails S _ digest hfail
  obtain ⟨committed, hstate, heval, _⟩ := SharedSigning.runProgram_support (commitBudget tau kappa) _
    (SharedSigner.commit_bounded S.signer salt root witness) world.other result hres
  rcases result with ⟨state, wd⟩
  dsimp only at hstate
  subst hstate
  simp only [preparedOf] at hobs ⊢
  have hpe := payload_eq S hpc salt root witness hsol _ _ _ committed heval digest ctr opening hobs
  simp only [Function.comp_apply, hobs]
  rw [← hpe]
  split
  · rename_i heq
    simp only [Spec.CandidateScheme.openSigning, hobs, PMF.pure_map, heq]
    try rfl
  · rename_i heq
    simp only [Spec.CandidateScheme.openSigning, hobs, PMF.pure_map, heq]
    try rfl

end
end SDitH.Proofs.DigestFirstVsSimulated
