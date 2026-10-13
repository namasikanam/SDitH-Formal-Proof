import SDitH.Proofs.SharedResample
import SDitH.Proofs.SimulationGapTrace

/-! The candidate scheme's oracles obey the resampling law. The honest
signing is a uniform salt and root, the commitment run on the inner
world, and a post-processing from the outer hash table (the
signature-level query and the body); the simulated signing is four
uniform draws, the commitment run and a pure post-processing; the public
oracle is a one-step run and a pure answer; so all three obey the law
by the generic shape. Key generation draws a uniform family at the empty
history, which is the posterior there, so it yields a resampled world. -/

namespace SDitH.Proofs.CandidateResample

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open CipherResample GameResample ChargeExpect SharedResample
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The payload of a commitment result. -/
def payloadOf (salt : Bits lambda) :
    Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
      (Bits lambda) (Bits lambda)
      (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) →
    Payload F lambda higherCount
  | Program.done committed => (stateOf S salt committed).1
  | _ => (fun _ => false, fun _ => 0)

/-- The signed state of a commitment result. -/
def signedOf (salt : Bits lambda) :
    Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))
      (Bits lambda) (Bits lambda)
      (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))) →
    SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount
  | Program.done committed => (stateOf S salt committed).2
  | _ => defaultState

/-- The body opened at a digest. -/
def bodyOf (state : SignedState F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
    (digest : Digest lambda) :
    Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount) :=
  match Spec.BLCRetry.observe (attempt state.key (S.expandEvaluation digest) S.encode) S.fuel 0 with
  | .returned counter opening => some (state.salt, state.auxiliary, (counter, opening), state.higher)
  | _ => none

/-- The honest post-processing: the signature-level query and the body. -/
def honestPost (pk message : List Bool) (salt : Bits lambda)
    (result : Program (List Bool)
      (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda)
      (Bits lambda) (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (table : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda)) :
    PMF (Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))) :=
  (Spec.RandomOracle.query table ⟨pk, message, payloadOf S salt result⟩).bind fun hr =>
    PMF.pure (⟨hr.1, bodyOf S (signedOf S salt result) hr.1⟩, hr.2)

/-- The honest signing in the program-running shape. -/
theorem honest_sign_shape (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message = fun (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) =>
      (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
        (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
          (runProgram (commitBudget tau kappa) (commitProgram S.signer salt root sk.2) world.other).bind fun r =>
            (honestPost S sk.1 message salt r.1 world.hashTable).map fun q => (q.1, ⟨q.2, r.2⟩) := by
  funext world
  simp only [scheme, Spec.CandidateScheme.components, prepareSigning, honestPost, PMF.bind_bind, PMF.bind_map,
    PMF.map_bind, Function.comp_def]
  congr 1
  funext salt
  congr 1
  funext root
  congr 1
  funext r
  rcases r with ⟨a, o⟩
  rcases a with committed | ⟨input, next⟩ | ⟨request, next⟩ <;>
    simp only [payloadOf, signedOf, bodyOf, Spec.CandidateScheme.openSigning, PMF.pure_map]
  all_goals congr 1

/-- The honest signing obeys the resampling law. -/
theorem honest_postLaw (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    PostLaw resample ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message) := by
  rw [honest_sign_shape]
  refine postLaw_sample _ _ _ fun salt => postLaw_sample _ _ _ fun root => ?_
  exact postLaw_run (commitBudget tau kappa) (commitProgram S.signer salt root sk.2) (honestPost S sk.1 message salt)

/-- The simulated post-processing. -/
def simPost (pk message : List Bool) (salt : Bits lambda) (digest : Digest lambda)
    (result : Program (List Bool)
      (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda)
      (Bits lambda) (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (table : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda)) :
    PMF (Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))) :=
  PMF.pure (match result with
    | Program.done committed =>
      let state := (stateOf S salt committed).2
      match Spec.BLCRetry.observe (attempt state.key (S.expandEvaluation digest) S.encode) S.fuel 0 with
      | .returned ctr opening =>
        let hidden := (S.expandEvaluation digest ctr).hidden
        let input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) :=
          ⟨pk, message, (committed.result.lines, simulatedCoefficients S salt committed hidden)⟩
        match table input with
        | none => (⟨digest, some (salt, committed.result.auxiliary, (ctr, opening), state.higher)⟩,
            Function.update table input (some digest))
        | some _ => (⟨digest, none⟩, table)
      | _ => (⟨digest, none⟩, table)
    | _ => (⟨digest, none⟩, table))

/-- The simulated signing in the program-running shape. -/
theorem simulated_sign_shape (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    (simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message = fun (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda)
        (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) =>
      (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
        (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
          (PMF.uniformOfFintype (Fin (selectorCount widths * w) → ZMod 2)).bind fun fake =>
            (PMF.uniformOfFintype (Digest lambda)).bind fun digest =>
              (runProgram (commitBudget tau kappa) (commitProgram S.signer salt root fake) world.other).bind fun r =>
                (simPost S sk.1 message salt digest r.1 world.hashTable).map fun q => (q.1, ⟨q.2, r.2⟩) := by
  funext world
  simp only [simulatedScheme, simulatedSign, simPost, PMF.map, Function.comp_def, PMF.pure_bind]
  congr 1
  funext salt
  congr 1
  funext root
  congr 1
  funext fake
  congr 1
  funext digest
  congr 1
  funext r
  rcases r with ⟨a, o⟩
  rcases a with committed | ⟨input, next⟩ | ⟨request, next⟩
  · dsimp only
    generalize Spec.BLCRetry.observe (attempt (stateOf S salt committed).2.key (S.expandEvaluation digest) S.encode)
      S.fuel 0 = obs
    rcases obs with ⟨c⟩ | ⟨ctr, opening⟩ | ⟨f⟩
    · rfl
    · dsimp only
      split <;> rename_i heq <;> simp only [heq]
    · rfl
  · rfl
  · rfl

/-- The simulated signing obeys the resampling law. -/
theorem simulated_postLaw (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    PostLaw resample ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message) := by
  rw [simulated_sign_shape]
  refine postLaw_sample _ _ _ fun salt => postLaw_sample _ _ _ fun root => postLaw_sample _ _ _ fun fake =>
    postLaw_sample _ _ _ fun digest => ?_
  exact postLaw_run (commitBudget tau kappa) (commitProgram S.signer salt root fake) (simPost S sk.1 message salt digest)

/-- The public oracle obeys the resampling law. -/
theorem publicOracle_postLaw (query : Query lambda) :
    PostLaw resample ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query) := by
  cases query with
  | hash input =>
    have h := postLaw_run (HashInput := HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Digest := Digest lambda) 1 (.hash input fun answer => .done answer.1)
      (fun (a : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
          (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) (Digest lambda)) table =>
        PMF.pure ((Answer.digest (match a with | .done value => value | _ => fun _ => false) :
        Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), table))
    convert h using 2
    simp only [scheme, Spec.CandidateScheme.components, publicOracle, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
      PMF.map]
    congr 1
    funext r
    rcases r with ⟨a, o⟩
    cases a <;> rfl
  | mask input =>
    have h := postLaw_run (HashInput := HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Digest := Digest lambda) 1 (.hash input fun answer => .done answer.2)
      (fun (a : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
          (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda)
          (Spec.SlopeConsistencyGame.Mask s (selectorCount widths * w) (lambda * (widths.length - 1)))) table =>
        PMF.pure ((Answer.mask (match a with | .done value => value | _ => 0) :
        Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), table))
    convert h using 2
    simp only [scheme, Spec.CandidateScheme.components, publicOracle, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
      PMF.map]
    congr 1
    funext r
    rcases r with ⟨a, o⟩
    cases a <;> rfl
  | cipher request =>
    have h := postLaw_run (HashInput := HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Digest := Digest lambda) 1 (.cipher request fun answer => .done answer)
      (fun (a : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
          (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) (Bits lambda)) table =>
        PMF.pure ((Answer.block (match a with | .done value => value | _ => fun _ => false) :
        Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), table))
    convert h using 2
    simp only [scheme, Spec.CandidateScheme.components, publicOracle, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
      PMF.map]
    congr 1
    funext r
    rcases r with ⟨a, o⟩
    cases a <;> rfl

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
theorem uniformOfFintype_congr {α : Type*} (i₁ i₂ : Fintype α) (n₁ n₂ : Nonempty α) :
    @PMF.uniformOfFintype α i₁ n₁ = @PMF.uniformOfFintype α i₂ n₂ := by
  cases Subsingleton.elim i₁ i₂
  rfl

/-- Key generation yields a resampled world. -/
theorem keygen_resampled :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).keygen =
      (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).keygen.bind fun g =>
        (resampleW resample g.2.2).map fun w => (g.1, g.2.1, w) := by
  simp only [scheme, Spec.CandidateScheme.components, Spec.SharedSigning.keygen, PMF.bind_map, PMF.map_bind, PMF.bind_bind, Function.comp_def]
  congr 1
  funext witness
  simp only [resampleW, resample, posterior_nil]
  rw [PMF.bind_const, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  show PMF.map _ (PMF.uniformOfFintype (Spec.IdealCipher.Family (Bits lambda) (Bits lambda))) = _
  refine congrArg₂ PMF.map ?_ (uniformOfFintype_congr _ _ _ _)
  rfl

end
end SDitH.Proofs.CandidateResample
