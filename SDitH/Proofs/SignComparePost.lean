import SDitH.Proofs.HonestToSimulated

/-! The per-signature comparison under any continuation. The bounds of the
honest signing against its digest-first form, of the digest-first form
against the fixed-witness simulated signing, and their chaining, hold for
every continuation applied to the signing's output: the proofs are the
same, with the continuation pushed through the binds, since the bodies
coincide off the events. This is the form the composition over the
signing game iterates. -/

namespace SDitH.Proofs.SignComparePost

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.HashCipherEvaluation Spec.SlopeConsistencyGame Spec.BLCRetry Spec.CandidateBAVC
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open SignStep SignCompare SimulatedWith DigestFirstBody DigestFirstVsSimulated HonestToSimulated CommitLinesEvent
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)

/-- The simulated signing's body at a salt, digest and run result. -/
def simBody (publicKey message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (salt : Bits lambda) (digest : Digest lambda)
    (result : Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda)
        (Bits lambda) (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) ×
      World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  match result.1 with
  | Program.done committed =>
    let state := (stateOf S salt committed).2
    match observe (attempt state.key (S.expandEvaluation digest) S.encode) S.fuel 0 with
    | .returned ctr opening =>
      let hidden := (S.expandEvaluation digest ctr).hidden
      let input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) :=
        ⟨publicKey, message, (committed.result.lines, simulatedCoefficients S salt committed hidden)⟩
      match world.hashTable input with
      | none => (⟨digest, some (salt, committed.result.auxiliary, (ctr, opening), state.higher)⟩,
          ⟨Function.update world.hashTable input (some digest), result.2⟩)
      | some _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)
    | _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)
  | _ => (⟨digest, none⟩, ⟨world.hashTable, result.2⟩)

variable {C : Type*}

/-- The fixed-witness simulated signing under a continuation, with the
digest drawn after the run. -/
theorem simulatedSignWith_bind (publicKey : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF C) :
    (simulatedSignWith S publicKey witness message world).bind h =
      (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
        (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
          (runProgram (commitBudget tau kappa) (commitProgram S.signer salt root witness) world.other).bind fun result =>
            (PMF.uniformOfFintype (Digest lambda)).bind fun digest =>
              h (simBody S publicKey message world salt digest result) := by
  unfold simulatedSignWith simBody
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext salt
  congr 1
  funext root
  exact PMF.bind_comm _ _ _

variable (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The honest signing under a continuation is within the input-present
event of its digest-first form. -/
theorem honest_le_digestFirst_post (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF C) (c : C) :
    (((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness) message
        world).bind h) c ≤
      ((digestFirstSign S publicKey witness message world).bind h) c + (inputPresent S publicKey witness message world) true := by
  show (((prepareSigning S publicKey witness message world.other).bind _).bind h) c ≤ _
  unfold digestFirstSign inputPresent
  rw [PMF.bind_bind, PMF.bind_bind]
  refine bind_le_bind_add_event _ _ _ _ (fun prepared _ hb => ?_) c
  have hnone : world.hashTable ⟨publicKey, message, prepared.1⟩ = none := by
    simpa using hb
  rw [hnone, query_bind_fresh' world.hashTable _ hnone]
  rfl

/-- The digest-first honest signing under a continuation is within the
retry-failure event of the fixed-witness simulated signing. -/
theorem digestFirst_le_simulatedWith_post (hpc : PayloadConsistent S) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (hsol : IsSolution S witness) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF C) (c : C) :
    ((digestFirstSign S publicKey witness message world).bind h) c ≤
      ((simulatedSignWith S publicKey witness message world).bind h) c +
        (retryEvent S publicKey witness message world) true := by
  rw [simulatedSignWith_bind]
  unfold digestFirstSign retryEvent
  rw [prepareSigning_eq]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine bind_le_bind_add_bind _ _ _ _ c (fun salt _ => ?_)
  refine bind_le_bind_add_bind _ _ _ _ c (fun root _ => ?_)
  refine bind_le_bind_add_bind _ _ _ _ c (fun result hres => ?_)
  refine bind_le_bind_add_event _ _ _ (fun digest => retryFails S (preparedOf S salt result).2.1 digest)
    (fun digest _ hfail => ?_) c
  obtain ⟨ctr, opening, hobs⟩ := returned_of_not_retryFails S _ digest hfail
  obtain ⟨committed, hstate, heval, _⟩ := SharedSigning.runProgram_support (commitBudget tau kappa) _
    (SharedSigner.commit_bounded S.signer salt root witness) world.other result hres
  rcases result with ⟨state, wd⟩
  dsimp only at hstate
  subst hstate
  simp only [preparedOf, simBody] at hobs ⊢
  have hpe := payload_eq S hpc salt root witness hsol _ _ _ committed heval digest ctr opening hobs
  simp only [hobs]
  rw [← hpe]
  split
  · rename_i heq
    simp only [Spec.CandidateScheme.openSigning, hobs, PMF.pure_map, PMF.pure_bind, heq]
    try rfl
  · rename_i heq
    simp only [Spec.CandidateScheme.openSigning, hobs, PMF.pure_map, PMF.pure_bind, heq]
    try rfl

/-- The honest signing under a continuation is within the input-present and
retry-failure events of the simulated signing at the honest witness. -/
theorem honest_le_simulatedWith_post (hpc : PayloadConsistent S) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (hsol : IsSolution S witness) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF C) (c : C) :
    (((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness) message
        world).bind h) c ≤
      ((simulatedSignWith S publicKey witness message world).bind h) c +
        ((inputPresent S publicKey witness message world) true + (retryEvent S publicKey witness message world) true) := by
  calc _ ≤ ((digestFirstSign S publicKey witness message world).bind h) c + (inputPresent S publicKey witness message world) true :=
        honest_le_digestFirst_post S V verifyBudget publicKey sampleWitness witness message world h c
    _ ≤ (((simulatedSignWith S publicKey witness message world).bind h) c + (retryEvent S publicKey witness message world) true) +
          (inputPresent S publicKey witness message world) true :=
        add_le_add_left (digestFirst_le_simulatedWith_post S publicKey hpc witness hsol message world h c) _
    _ = _ := by ring

/-- With the witness swap as an explicit term under continuations, the honest
signing under a continuation is within the two events plus the swap term of
the simulated scheme's signing. -/
theorem honest_le_simulated_post (hpc : PayloadConsistent S) (witness : Fin (selectorCount widths * w) → ZMod 2)
    (hsol : IsSolution S witness) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
      (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (h : Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF C)
    (epsSwap : ℝ≥0∞)
    (hswap : ∀ (fake : Fin (selectorCount widths * w) → ZMod 2) (c : C),
      ((simulatedSignWith S publicKey witness message world).bind h) c ≤
        ((simulatedSignWith S publicKey fake message world).bind h) c + epsSwap)
    (c : C) :
    (((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (publicKey, witness) message
        world).bind h) c ≤
      (((simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message world).bind h) c +
        ((inputPresent S publicKey witness message world) true + (retryEvent S publicKey witness message world) true +
          epsSwap) := by
  have hsim : (simulatedScheme S V verifyBudget publicKey sampleWitness).sign (publicKey, witness) message world =
      simulatedSign S publicKey message world := rfl
  rw [hsim, simulatedSign_eq_with, PMF.bind_bind]
  calc _ ≤ ((simulatedSignWith S publicKey witness message world).bind h) c +
        ((inputPresent S publicKey witness message world) true + (retryEvent S publicKey witness message world) true) :=
        honest_le_simulatedWith_post S V verifyBudget publicKey sampleWitness hpc witness hsol message world h c
    _ ≤ (((PMF.uniformOfFintype (Fin (selectorCount widths * w) → ZMod 2)).bind fun fake =>
          (simulatedSignWith S publicKey fake message world).bind h) c + epsSwap) +
        ((inputPresent S publicKey witness message world) true + (retryEvent S publicKey witness message world) true) :=
        add_le_add_left (le_bind_add_const _ _ _ epsSwap c (fun fake _ => hswap fake c)) _
    _ = _ := by ring

end
end SDitH.Proofs.SignComparePost
