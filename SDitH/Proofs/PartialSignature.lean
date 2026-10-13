import SDitH.Spec.PartialSignature
import SDitH.Proofs.PartialBLCRetry
import SDitH.Proofs.BLCRecompute

namespace SDitH.Proofs.PartialSignature

open Spec.PartialSignature Spec.SignatureComposition Spec.ConcreteChallenges Spec.DomainSeparation

section Signing

variable {F Aux : Type*} [Field F] [DecidableEq F]
  {lambda tau kappa wpow higherCount : Nat}
  (prepared : Prepared F Aux lambda tau (2 ^ kappa) higherCount)

omit [DecidableEq F] in
theorem finishSigning_returned_iff (observation : Spec.PartialBLCRetry.Observation lambda tau kappa)
    (signature : Signature F Aux lambda tau higherCount) :
    finishSigning prepared observation = .returned signature ↔
      ∃ counter opening, observation = .returned counter opening ∧
        attachOpening prepared counter opening = signature := by
  cases observation <;> simp [finishSigning]

/-- Every emitted signature retains the actual opening and the challenge which
passed the source checks, as well as all fields computed before the retry loop. -/
theorem observeSigning_returned (Topen : Nat)
    (expand : Digest lambda → Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat)
    (signature : Signature F Aux lambda tau higherCount)
    (h : Spec.PartialSignature.observeSigning prepared Topen expand encode fuel = .returned signature) :
    ∃ counter opening challenge cursor,
      signature = attachOpening prepared counter opening ∧
      expand prepared.piop counter = .returned challenge cursor ∧
      Spec.BAVC.openCommitment prepared.key challenge.hidden Topen = .ok opening ∧
      Spec.BLCRetry.GrindingPassed challenge.grinding ∧ encode challenge.hidden ≠ 0 := by
  obtain ⟨counter, opening, ho, hs⟩ := (finishSigning_returned_iff prepared _ signature).mp h
  obtain ⟨_, challenge, cursor, he, hb, hg, hn⟩ := PartialBLCRetry.observe_returned
    prepared.key Topen (expand prepared.piop) encode fuel 0 counter opening ho
  exact ⟨counter, opening, challenge, cursor, hs.symm, he, hb, hg, hn⟩

theorem observeSigning_returned_stable (Topen : Nat)
    (expand : Digest lambda → Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel extra : Nat)
    (signature : Signature F Aux lambda tau higherCount)
    (h : Spec.PartialSignature.observeSigning prepared Topen expand encode fuel = .returned signature) :
    Spec.PartialSignature.observeSigning prepared Topen expand encode (fuel + extra) = .returned signature := by
  obtain ⟨counter, opening, ho, hs⟩ := (finishSigning_returned_iff prepared _ signature).mp h
  apply (finishSigning_returned_iff prepared _ signature).mpr
  exact ⟨counter, opening, PartialBLCRetry.observe_returned_stable prepared.key Topen
    (expand prepared.piop) encode fuel extra 0 counter opening ho, hs⟩

theorem observeSigning_total (Topen : Nat)
    (expand : Digest lambda → Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (cursor : Spec.BLCRetry.Counter → Spec.ByteSampling.Reader)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (fuel : Nat) :
    Spec.PartialSignature.observeSigning prepared Topen
      (fun digest ctr => .returned (expand digest ctr) (cursor ctr)) encode fuel =
      liftTotalSigning (Spec.SignatureComposition.observeSigning prepared Topen expand encode fuel) := by
  rw [Spec.PartialSignature.observeSigning, PartialBLCRetry.observe_total]
  unfold Spec.SignatureComposition.observeSigning Spec.BLCRetry.openRandomEvaluation
  cases Spec.BLCRetry.observe (Spec.BLCRetry.attempt prepared.key Topen (expand prepared.piop) encode) fuel 0 <;> rfl

theorem observeSigning_no_return (Topen : Nat)
    (expand : Digest lambda → Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
    (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hn : ∀ ctr challenge cursor, expand prepared.piop ctr ≠ .returned challenge cursor)
    (fuel : Nat) (signature : Signature F Aux lambda tau higherCount) :
    Spec.PartialSignature.observeSigning prepared Topen expand encode fuel ≠ .returned signature := by
  intro h
  obtain ⟨counter, _, challenge, cursor, _, he, _⟩ :=
    observeSigning_returned prepared Topen expand encode fuel signature h
  exact hn counter challenge cursor he

end Signing

section HashSigning

variable {F Aux : Type*} [Field F] [DecidableEq F]
  (category : Spec.FieldRepresentation.Category) {tau kappa higherCount : Nat} (wpow : Nat)
  (prepared : Prepared F Aux (Spec.FieldRepresentation.width category) tau (2 ^ kappa) higherCount)
  (Topen : Nat) (encoding : CounterEncoding)
  (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel count : Nat)
  (enough : wpow ≤ 8 * count)

theorem hashSigning_eq_observe :
    hashSigning category wpow prepared Topen encoding encode innerFuel outerFuel count enough =
      Spec.PartialSignature.observeSigning prepared Topen
        (fun digest ctr => hashEvaluation category tau kappa wpow encoding digest ctr innerFuel count enough)
        encode outerFuel := rfl

theorem hashSigning_no_return (ht : 0 < tau)
    (signature : Signature F Aux (Spec.FieldRepresentation.width category) tau higherCount) :
    hashSigning category wpow prepared Topen encoding encode innerFuel outerFuel count enough ≠
      .returned signature := by
  intro h
  obtain ⟨counter, opening, ho, _⟩ := (finishSigning_returned_iff prepared _ signature).mp h
  exact PartialBLCRetry.hashOpen_no_return category tau kappa wpow ht prepared.key Topen
    encoding prepared.piop encode innerFuel outerFuel count enough counter opening ho

/-- This applies to every prepared record, including actual BLC/PIOP output.
The missing source assignment is reached before a signature can be emitted. -/
theorem hashSigning_missing (ht : 0 < tau) (hk : kappa ≤ 32) :
    let src := Spec.SHAKE.reader category (evaluationInput encoding prepared.piop 0)
    hashSigning category wpow prepared Topen encoding encode (innerFuel + 1) (outerFuel + 1) count enough =
      .undefinedExpansion 0 ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src) := by
  dsimp only
  rw [hashSigning, PartialBLCRetry.hashOpen_missing category tau kappa wpow ht hk]
  rfl

end HashSigning

section Verification

variable {F : Type} {lambda tau kappa B wit rnd : Nat}

theorem finishRecompute_boundary_iff
    (result : Except Spec.BLCRecompute.Error
      (Spec.BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd))
    (state : Spec.BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd) :
    finishRecompute result = .consistencyBoundary state ↔ result = .ok state := by
  cases result with
  | ok value => simp [finishRecompute]
  | error cause => cases cause <;> simp [finishRecompute]

theorem finishRecompute_rejected_iff
    (result : Except Spec.BLCRecompute.Error
      (Spec.BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd)) :
    finishRecompute result = .rejected ↔ result = .error .headerRejected := by
  cases result with
  | ok value => simp [finishRecompute]
  | error cause => cases cause <;> simp [finishRecompute]

variable [Field F] [DecidableEq F] {wpow higherCount : Nat}
  (p : Spec.BLCCommit.Primitives lambda tau kappa (lambda + B) wit rnd)
  (signature : Signature F (Spec.BLCCommit.Auxiliary tau (lambda + B) wit rnd) lambda tau higherCount)
  (expand : Digest lambda → Spec.BLCRetry.Counter → EvaluationObservation tau kappa wpow)
  (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
  (bindings : Spec.BLCRecompute.Bindings lambda tau kappa ((lambda + B) + (wit + rnd)))
  (randomCount consistencyCount : Nat)
  (hrandom : (lambda + B) + (wit + rnd) ≤ 8 * randomCount)
  (hconsistency : wit + rnd ≤ 8 * consistencyCount)

theorem recompute_total
    (total : Digest lambda → Spec.BLCRetry.Counter → Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (cursor : Spec.BLCRetry.Counter → Spec.ByteSampling.Reader) :
    recompute p signature (fun digest ctr => .returned (total digest ctr) (cursor ctr))
      encode Topen bindings randomCount consistencyCount hrandom hconsistency =
      finishRecompute (Spec.BLCRecompute.prepareWithBindings p signature.salt signature.auxiliary
        signature.decomposition (total signature.piop) encode Topen bindings
        randomCount consistencyCount hrandom hconsistency) := rfl

theorem recompute_boundary_iff
    (state : Spec.BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd) :
    recompute p signature expand encode Topen bindings randomCount consistencyCount hrandom hconsistency =
      .consistencyBoundary state ↔
      ∃ challenge cursor,
        expand signature.piop signature.decomposition.1 = .returned challenge cursor ∧
        Spec.BLCRecompute.prepareWithBindings p signature.salt signature.auxiliary signature.decomposition
          (fun _ => challenge) encode Topen bindings randomCount consistencyCount hrandom hconsistency = .ok state := by
  cases he : expand signature.piop signature.decomposition.1 <;>
    simp [recompute, he, finishRecompute_boundary_iff]

theorem recompute_boundary_nonzero
    (state : Spec.BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd)
    (h : recompute p signature expand encode Topen bindings randomCount consistencyCount hrandom hconsistency =
      .consistencyBoundary state) : state.delta = state.deltaInv⁻¹ ∧ state.delta ≠ 0 := by
  obtain ⟨challenge, _, _, hp⟩ := (recompute_boundary_iff p signature expand encode Topen bindings
    randomCount consistencyCount hrandom hconsistency state).mp h
  exact (BLCRecompute.prepare_delta_nonzero p signature.salt signature.auxiliary signature.decomposition
    (fun _ => challenge) encode Topen bindings randomCount consistencyCount hrandom hconsistency state hp).2

theorem recompute_absent_no_boundary (ht : 0 < tau) (hn : 1 < 2 ^ kappa)
    (state : Spec.BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B) wit rnd) :
    recompute p signature expand encode Topen Spec.BLCRecompute.absentBindings
      randomCount consistencyCount hrandom hconsistency ≠ .consistencyBoundary state := by
  intro h
  obtain ⟨challenge, _, _, hp⟩ := (recompute_boundary_iff p signature expand encode Topen
    Spec.BLCRecompute.absentBindings randomCount consistencyCount hrandom hconsistency state).mp h
  exact BLCRecompute.prepare_absent_no_return p signature.salt signature.auxiliary signature.decomposition
    (fun _ => challenge) encode Topen randomCount consistencyCount hrandom hconsistency ht hn state hp

theorem recompute_header_rejected (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (cursor : Spec.ByteSampling.Reader)
    (he : expand signature.piop signature.decomposition.1 = .returned challenge cursor)
    (hg : ¬ (Spec.BLCRetry.GrindingPassed challenge.grinding ∧ encode challenge.hidden ≠ 0)) :
    recompute p signature expand encode Topen bindings randomCount consistencyCount hrandom hconsistency =
      .rejected := by
  rw [recompute, he]
  dsimp only
  rw [BLCRecompute.prepare_header_rejected p signature.salt signature.auxiliary
    signature.decomposition (fun _ => challenge) encode Topen bindings randomCount consistencyCount
    hrandom hconsistency hg]
  rfl

/-- A failed BAVC reconstruction is not the verifier's explicit Reject.
The undefined tuple read and its actual underlying cause are retained. -/
theorem recompute_reconstruction_error (challenge : Spec.BLCRetry.Challenge tau (2 ^ kappa) wpow)
    (cursor : Spec.ByteSampling.Reader)
    (he : expand signature.piop signature.decomposition.1 = .returned challenge cursor)
    (cause : Spec.BAVC.ReconstructionError)
    (hg : Spec.BLCRetry.GrindingPassed challenge.grinding ∧ encode challenge.hidden ≠ 0)
    (hb : Spec.BAVC.reconstructWithNodes
      (Spec.SeedPrimitives.bavcPrimitives (tau * (2 ^ kappa)) p.grinding p.encStar p.hash)
      signature.salt challenge.hidden signature.decomposition.2 Topen bindings.nodes = .error cause) :
    recompute p signature expand encode Topen bindings randomCount consistencyCount hrandom hconsistency =
      .undefinedRecomputation (.undefinedReconstructionResult cause) := by
  rw [recompute, he]
  dsimp only
  rw [BLCRecompute.prepare_reconstruction_error p signature.salt signature.auxiliary
    signature.decomposition (fun _ => challenge) encode Topen bindings randomCount consistencyCount
    hrandom hconsistency cause hg hb]
  rfl

end Verification

section HashVerification

variable {F : Type} [Field F] [DecidableEq F]
  (category : Spec.FieldRepresentation.Category) {tau kappa B wit rnd higherCount : Nat} (wpow : Nat)
  (p : Spec.BLCCommit.Primitives (Spec.FieldRepresentation.width category) tau kappa
    (Spec.FieldRepresentation.width category + B) wit rnd)
  (signature : Signature F (Spec.BLCCommit.Auxiliary tau (Spec.FieldRepresentation.width category + B) wit rnd)
    (Spec.FieldRepresentation.width category) tau higherCount)
  (encoding : CounterEncoding) (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
  (bindings : Spec.BLCRecompute.Bindings (Spec.FieldRepresentation.width category) tau kappa
    ((Spec.FieldRepresentation.width category + B) + (wit + rnd)))
  (randomCount consistencyCount : Nat)
  (hrandom : (Spec.FieldRepresentation.width category + B) + (wit + rnd) ≤ 8 * randomCount)
  (hconsistency : wit + rnd ≤ 8 * consistencyCount)
  (fuel count : Nat) (enough : wpow ≤ 8 * count)

theorem hashRecompute_missing (ht : 0 < tau) (hk : kappa ≤ 32) :
    let src := Spec.SHAKE.reader category (evaluationInput encoding signature.piop signature.decomposition.1)
    hashRecompute category wpow p signature encoding encode Topen bindings randomCount consistencyCount
      hrandom hconsistency (fuel + 1) count enough =
      .undefinedExpansion ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src) := by
  dsimp only
  rw [hashRecompute, recompute, ConcreteChallenges.hashEvaluation_missing category tau kappa wpow ht hk]

theorem hashRecompute_no_boundary (ht : 0 < tau)
    (state : Spec.BLCRecompute.ConsistencyBoundary F (Spec.FieldRepresentation.width category)
      tau kappa (Spec.FieldRepresentation.width category + B) wit rnd) :
    hashRecompute category wpow p signature encoding encode Topen bindings randomCount consistencyCount
      hrandom hconsistency fuel count enough ≠ .consistencyBoundary state := by
  intro h
  obtain ⟨challenge, cursor, he, _⟩ := (recompute_boundary_iff p signature _ encode Topen bindings
    randomCount consistencyCount hrandom hconsistency state).mp h
  exact ConcreteChallenges.hashEvaluation_no_return category tau kappa wpow ht encoding
    signature.piop signature.decomposition.1 fuel count enough challenge cursor he

theorem hashRecompute_no_rejection (ht : 0 < tau) :
    hashRecompute category wpow p signature encoding encode Topen bindings randomCount consistencyCount
      hrandom hconsistency fuel count enough ≠ .rejected := by
  unfold hashRecompute recompute
  cases he : hashEvaluation category tau kappa wpow encoding signature.piop
      signature.decomposition.1 fuel count enough with
  | pending state => simp [he]
  | undefinedIntegerAssignment state candidate => simp [he]
  | returned challenge cursor =>
    exact False.elim (ConcreteChallenges.hashEvaluation_no_return category tau kappa wpow ht encoding
      signature.piop signature.decomposition.1 fuel count enough challenge cursor he)

end HashVerification

/-- The independently supplied line-21 base reaches the exact printed final
hash comparison through actual recomputation and PIOP suffixes. No claim that
this base is the output of the literal line 21 is part of the theorem. -/
theorem verifySuffix_accept_iff {F : Type} [Field F] [Algebra (ZMod 2) F]
    {r k w lambda tau kappa B higherCount : Nat}
    (widths : List Nat) (hdegree : widths.length = higherCount + 1)
    (hsize : Spec.PIOPArithmetic.leafCount widths * w = r + k) (xi : F)
    (expandBatching : Digest lambda → (Fin (Spec.Batching.blockCount r lambda) → F) × (Fin w → F))
    (hashPiop : HashInput F lambda higherCount → Digest lambda)
    (hashLines : Spec.BLCRecompute.LinesHashInput lambda tau kappa (lambda + B) → Digest lambda)
    (H' : Matrix (Fin r) (Fin k) (ZMod 2)) (y : Fin r → ZMod 2)
    (publicKey message : List Bool)
    (signature : Signature F (Spec.BLCCommit.Auxiliary tau (lambda + B)
      (Spec.PIOPArithmetic.selectorCount widths * w) (lambda * (widths.length - 1))) lambda tau higherCount)
    (state : Spec.BLCRecompute.ConsistencyBoundary F lambda tau kappa (lambda + B)
      (Spec.PIOPArithmetic.selectorCount widths * w) (lambda * (widths.length - 1)))
    (base : Fin (lambda + B) → Fin tau → Fin kappa → ZMod 2) :
    verifySuffix widths hdegree hsize xi expandBatching hashPiop hashLines H' y publicKey message
      signature state base = true ↔
      hashPiop (verificationInput widths hdegree hsize xi expandBatching H' y publicKey message signature
        (Spec.BLCRecompute.suffix xi hashLines state base)) = signature.piop := by
  simp only [verifySuffix, verifyPostRecompute, decide_eq_true_eq]

end SDitH.Proofs.PartialSignature
