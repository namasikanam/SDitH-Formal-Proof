import SDitH.Proofs.ExtractionSplit

/-! The solver and the simulated statement. The solver runs the fork
experiment of a scheme at a uniformly random index and outputs the
extracted witness of the first branch (the corrections plus the slope at
the first execution); whenever the solution event holds, that output is a
solution of the public instance. For any scheme sharing the candidate
scheme's types (the intended one is a witness-free simulator, still to be
named), per-event simulation gaps transfer the forgery bound to the
simulated events and the solver's success. The named simulator and its
gaps remain open. -/

namespace SDitH.Proofs.SimulatedSolver

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SignatureQuerySelection Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier
open Spec.PIOPArithmetic (selectorCount)
open SharedTargetBound (digestInv)
open SharedMentionBound (epsilonM)
open SharedCollisionBound (epsilonC)
open CandidateReduction ForgeryReduction ExtractionSplit
open PIOPExtraction (extractedWitness)
open scoped Classical ENNReal
noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
  (sim : Scheme (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
    (Signature (Spec.BAVC.Digest lambda) (Option (Bod F lambda tau kappa s higherCount w widths)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
    (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))

/-- An event's random-index probability in a scheme's fork experiment. -/
def simEventExperiment (E : Snap F lambda s higherCount w widths State →
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (fuel : Nat) : PMF Bool :=
  (PMF.uniformOfFintype (Fin (fuel + 1))).bind fun index =>
    (cutExperiment sim adversary index.val (fuel + 1)).bind fun c => match c with
      | .ended _ => PMF.pure false
      | .saved snapshot => (forkAt sim adversary snapshot).map (E snapshot)

/-- The solver's output on a fork result: the extracted witness of the first
branch with the slope at the first execution. -/
def solverOutput (htau : 0 < tau) (_snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) →
      Option (Fin (selectorCount widths * w) → ZMod 2)
  | none => none
  | some (l, r) =>
    match l.checked.terminal, r.checked.terminal with
    | .attempt a, .attempt b =>
      match a.signature.body, b.signature.body with
      | some bodyA, some bodyB => some (extractedWitness bodyA.2.1 (slopesOf S V a bodyA bodyB ⟨0, htau⟩))
      | _, _ => none
    | _, _ => none

/-- The solver: the fork experiment of the scheme at a random index with the
extracted output. -/
def solver (htau : 0 < tau) (fuel : Nat) : PMF (Option (Fin (selectorCount widths * w) → ZMod 2)) :=
  (PMF.uniformOfFintype (Fin (fuel + 1))).bind fun index =>
    (cutExperiment sim adversary index.val (fuel + 1)).bind fun c => match c with
      | .ended _ => PMF.pure none
      | .saved snapshot => (forkAt sim adversary snapshot).map (solverOutput S V htau snapshot)

/-- The solver's success: its output is a solution of the public instance. -/
def solverSuccess (htau : 0 < tau) (fuel : Nat) : ℝ≥0∞ :=
  ((solver S V adversary sim htau fuel).map fun out => decide (∃ bits, out = some bits ∧ IsSolution S bits)) true

omit [NeZero tau] in
theorem rsdSolved_output (htau : 0 < tau) (snapshot : Snap F lambda s higherCount w widths State) (result)
    (h : rsdSolved S V snapshot result = true) :
    ∃ bits, solverOutput S V htau snapshot result = some bits ∧ IsSolution S bits := by
  obtain ⟨l, r, a, b, bodyA, bodyB, u, rfl, ha, hb, hbodyA, hbodyB, hu, hsol⟩ := rsdSolved_solution S V snapshot result h
  refine ⟨extractedWitness bodyA.2.1 (slopesOf S V a bodyA bodyB ⟨0, htau⟩), ?_, ?_⟩
  · simp only [solverOutput, ha, hb, hbodyA, hbodyB]
  · have hw : extractedWitness bodyA.2.1 (slopesOf S V a bodyA bodyB ⟨0, htau⟩) = extractedWitness bodyA.2.1 u := by
      congr 1
      funext c'
      exact hu _ c'
    rw [hw]
    exact hsol

omit [NeZero tau] in
/-- The solution event is at most the solver's success. -/
theorem solverSuccess_ge (htau : 0 < tau) (fuel : Nat) :
    (simEventExperiment adversary sim (rsdSolved S V) fuel) true ≤ solverSuccess S V adversary sim htau fuel := by
  unfold solverSuccess solver simEventExperiment
  rw [PMF.map_bind]
  refine bind_true_mono _ _ _ fun index _ => ?_
  rw [PMF.map_bind]
  refine bind_true_mono _ _ _ fun c _ => ?_
  cases c with
  | ended terminal => simp
  | saved snapshot =>
    rw [PMF.map_comp]
    refine ForkCutRun.map_true_mono _ _ _ fun result h => ?_
    obtain ⟨bits, hout, hsol⟩ := rsdSolved_output S V htau snapshot result h
    simp only [Function.comp, decide_eq_true_eq]
    exact ⟨bits, hout, hsol⟩

/-- The forgery bound in terms of a scheme's events and the solver's success,
given a uniform per-event simulation gap between the candidate scheme and
that scheme. -/
theorem forgery_le_simulated (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (bound : Nat) (hcommit : Spec.SharedSigner.commitBudget tau kappa ≤ bound) (hverify : verifyBudget ≤ bound)
    (hone : 1 ≤ bound) (fuel : Nat) (epsSim : ℝ≥0∞)
    (hgap : ∀ E, (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary sim E fuel) true + epsSim) :
    (advantage (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary (fuel + 1) -
        digestInv lambda) ^ 2 ≤
      ((fuel + 1 : Nat) : ℝ≥0∞) ^ 2 *
        (((simEventExperiment adversary sim maskAfter fuel) true + epsSim) +
         ((simEventExperiment adversary sim (fun _ => notSeparated V) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (seedCollision V) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (fun _ => slopeWin S V) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (fun _ => zeroChallenge V encode) fuel) true + epsSim) +
         ((simEventExperiment adversary sim (schwartzZippel S V encode) fuel) true + epsSim) +
         (((simEventExperiment adversary sim (batchingBad S V) fuel) true + epsSim) +
          (solverSuccess S V adversary sim htau fuel + epsSim)) +
         ((fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
            epsilonM lambda tau bound ((fuel + 1) * (bound + bound))) +
          (fuel + 1) * (epsilonC lambda bound ((fuel + 1) * (bound + bound)) +
            epsilonC lambda bound ((fuel + 1) * (bound + bound))) +
          (2 : ℝ≥0∞) * ((fuel + 1) * (bound * digestInv lambda + bound * digestInv lambda) +
            (fuel + 1) * (epsilonM lambda tau bound ((fuel + 1) * (bound + bound)) +
              epsilonM lambda tau bound ((fuel + 1) * (bound + bound))))) +
         digestInv lambda) := by
  refine (forgery_le_events_split S V verifyBudget publicKey sampleWitness adversary hlambda htau encode hmid hencoding
    hlinesEnc hencode bound hcommit hverify hone fuel).trans (mul_le_mul_right ?_ _)
  refine add_le_add_left (add_le_add_left ?_ _) _
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (hgap _) (hgap _)) (hgap _)) (hgap _))
    (hgap _)) (hgap _)) (add_le_add (hgap _) ((hgap _).trans (add_le_add_left (solverSuccess_ge S V adversary sim htau fuel) _)))

end
end SDitH.Proofs.SimulatedSolver
