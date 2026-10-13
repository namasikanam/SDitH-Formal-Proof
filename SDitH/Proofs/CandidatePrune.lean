import SDitH.Proofs.PruneLawRun
import SDitH.Proofs.CandidatePrepLaw

/-! The candidate scheme's oracles obey the prune law, grow and keep
consistency. Each is program-shaped: the honest and simulated signings are
uniform draws, the commitment run and a post-processing from the outer
table; the public oracle is a one-step run with a pure answer; the
verification preparation is a pure rejection or the verification run with a
pure answer. The simulated scheme shares the public oracle and the
verification preparation with the candidate scheme. -/

namespace SDitH.Proofs.CandidatePrune

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open CipherResample GameResample ChargeExpect SharedResample CandidateResample CandidatePrepLaw
open GamePrune PruneLawRun
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  (K : List (Bits lambda))

/-- The public oracle at a hash query as a program-shaped oracle. -/
theorem publicOracle_hash_eq (input : List Bool) :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle (.hash input) =
      runOracle 1 (.hash input fun answer => .done answer.1)
        (fun (a : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
            (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) (Digest lambda)) table =>
          PMF.pure ((Answer.digest (match a with | .done value => value | _ => fun _ => false) :
            Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), table)) := by
  funext world
  simp only [scheme, Spec.CandidateScheme.components, publicOracle, runOracle, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def, PMF.map]
  congr 1
  funext r
  rcases r with ⟨a, o⟩
  cases a <;> rfl

/-- The public oracle at a mask query as a program-shaped oracle. -/
theorem publicOracle_mask_eq (input : List Bool) :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle (.mask input) =
      runOracle 1 (.hash input fun answer => .done answer.2)
        (fun (a : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
            (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda)
            (Spec.SlopeConsistencyGame.Mask s (selectorCount widths * w) (lambda * (widths.length - 1)))) table =>
          PMF.pure ((Answer.mask (match a with | .done value => value | _ => 0) :
            Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), table)) := by
  funext world
  simp only [scheme, Spec.CandidateScheme.components, publicOracle, runOracle, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def, PMF.map]
  congr 1
  funext r
  rcases r with ⟨a, o⟩
  cases a <;> rfl

/-- The public oracle at a cipher query as a program-shaped oracle. -/
theorem publicOracle_cipher_eq (request : Spec.IdealCipher.Query (Bits lambda) (Bits lambda)) :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle (.cipher request) =
      runOracle 1 (.cipher request fun answer => .done answer)
        (fun (a : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s (selectorCount widths * w)
            (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) (Bits lambda)) table =>
          PMF.pure ((Answer.block (match a with | .done value => value | _ => fun _ => false) :
            Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))), table)) := by
  funext world
  simp only [scheme, Spec.CandidateScheme.components, publicOracle, runOracle, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def, PMF.map]
  congr 1
  funext r
  rcases r with ⟨a, o⟩
  cases a <;> rfl

/-- The verification preparation of a bodiless signature is a pure rejection. -/
theorem prepareVerification_none_eq (pk message : List Bool) (piop : Digest lambda) :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification pk message
        ⟨piop, none⟩ = fun w => PMF.pure (none, w) := by
  funext world
  simp only [scheme, Spec.CandidateScheme.components, Spec.CandidateScheme.prepareVerification, PMF.pure_map]
  rfl

/-- The verification preparation of a signature with a body as a
program-shaped oracle. -/
theorem prepareVerification_some_eq (pk message : List Bool) (piop : Digest lambda)
    (body : Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount) :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification pk message
        ⟨piop, some body⟩ =
      runOracle verifyBudget (verifyProgram V body.1 body.2.1 piop body.2.2.1)
        (fun a table => PMF.pure ((verifyAnswer S pk message piop body a).map
          (fun payload => (⟨pk, message, payload⟩ : HashInput (List Bool) (List Bool) (Payload F lambda higherCount))),
          table)) := by
  funext world
  simp only [scheme, Spec.CandidateScheme.components, Spec.CandidateScheme.prepareVerification, runOracle,
    PMF.bind_bind, PMF.pure_bind, Function.comp_def, PMF.map]
  congr 1
  funext r
  rcases r with ⟨a, o⟩
  cases a with
  | done e => cases e <;> rfl
  | hash _ _ => rfl
  | cipher _ _ => rfl

section Candidate

/-- The candidate scheme's honest signing obeys the prune law. -/
theorem honest_pruneLaw (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    PruneLaw K ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message) := by
  rw [honest_sign_shape]
  refine pruneLaw_sample _ _ _ fun salt => pruneLaw_sample _ _ _ fun root => ?_
  exact pruneLaw_run K (commitBudget tau kappa) (commitProgram S.signer salt root sk.2) (honestPost S sk.1 message salt)

theorem honest_grows (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    Grows ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message) := by
  rw [honest_sign_shape]
  refine grows_sample _ _ fun salt => grows_sample _ _ fun root => ?_
  exact grows_run (commitBudget tau kappa) (commitProgram S.signer salt root sk.2) (honestPost S sk.1 message salt)

theorem honest_keeps (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    Keeps ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message) := by
  rw [honest_sign_shape]
  refine keeps_sample _ _ fun salt => keeps_sample _ _ fun root => ?_
  exact keeps_run (commitBudget tau kappa) (commitProgram S.signer salt root sk.2) (honestPost S sk.1 message salt)

/-- The simulated signing obeys the prune law. -/
theorem simulated_pruneLaw (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    PruneLaw K ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message) := by
  rw [simulated_sign_shape]
  refine pruneLaw_sample _ _ _ fun salt => pruneLaw_sample _ _ _ fun root => pruneLaw_sample _ _ _ fun fake =>
    pruneLaw_sample _ _ _ fun digest => ?_
  exact pruneLaw_run K (commitBudget tau kappa) (commitProgram S.signer salt root fake) (simPost S sk.1 message salt digest)

theorem simulated_grows (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    Grows ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message) := by
  rw [simulated_sign_shape]
  refine grows_sample _ _ fun salt => grows_sample _ _ fun root => grows_sample _ _ fun fake =>
    grows_sample _ _ fun digest => ?_
  exact grows_run (commitBudget tau kappa) (commitProgram S.signer salt root fake) (simPost S sk.1 message salt digest)

theorem simulated_keeps (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) :
    Keeps ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message) := by
  rw [simulated_sign_shape]
  refine keeps_sample _ _ fun salt => keeps_sample _ _ fun root => keeps_sample _ _ fun fake =>
    keeps_sample _ _ fun digest => ?_
  exact keeps_run (commitBudget tau kappa) (commitProgram S.signer salt root fake) (simPost S sk.1 message salt digest)

/-- The public oracle obeys the prune law. -/
theorem publicOracle_pruneLaw (query : Query lambda) :
    PruneLaw K ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query) := by
  cases query with
  | hash input => rw [publicOracle_hash_eq]; exact pruneLaw_run _ _ _ _
  | mask input => rw [publicOracle_mask_eq]; exact pruneLaw_run _ _ _ _
  | cipher request => rw [publicOracle_cipher_eq]; exact pruneLaw_run _ _ _ _

theorem publicOracle_grows (query : Query lambda) :
    Grows ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query) := by
  cases query with
  | hash input => rw [publicOracle_hash_eq]; exact grows_run _ _ _
  | mask input => rw [publicOracle_mask_eq]; exact grows_run _ _ _
  | cipher request => rw [publicOracle_cipher_eq]; exact grows_run _ _ _

theorem publicOracle_keeps (query : Query lambda) :
    Keeps ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query) := by
  cases query with
  | hash input => rw [publicOracle_hash_eq]; exact keeps_run _ _ _
  | mask input => rw [publicOracle_mask_eq]; exact keeps_run _ _ _
  | cipher request => rw [publicOracle_cipher_eq]; exact keeps_run _ _ _

/-- The verification preparation obeys the prune law. -/
theorem prepareVerification_pruneLaw (pk message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))) :
    PruneLaw K ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification
      pk message signature) := by
  rcases signature with ⟨piop, _ | body⟩
  · rw [prepareVerification_none_eq]; exact pruneLaw_pure _ _
  · rw [prepareVerification_some_eq]; exact pruneLaw_run _ _ _ _

theorem prepareVerification_grows (pk message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount))) :
    Grows ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification
      pk message signature) := by
  rcases signature with ⟨piop, _ | body⟩
  · rw [prepareVerification_none_eq]; exact grows_pure _
  · rw [prepareVerification_some_eq]; exact grows_run _ _ _

/-- The simulated scheme's public oracle and verification preparation are
the candidate scheme's. -/
theorem simulated_publicOracle_eq :
    (simulatedScheme S V verifyBudget publicKey sampleWitness).publicOracle =
      (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle := rfl

theorem simulated_prepareVerification_eq :
    (simulatedScheme S V verifyBudget publicKey sampleWitness).prepareVerification =
      (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification := rfl

end Candidate

end
end SDitH.Proofs.CandidatePrune
