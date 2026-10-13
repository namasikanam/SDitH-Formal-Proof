import SDitH.Spec.CipherSignature
import SDitH.Proofs.CipherBLCRetry
import SDitH.Proofs.PartialSignature

namespace SDitH.Proofs.CipherSignature

open Spec.CipherSignature Spec.CipherEvaluation Spec.ConcreteChallenges Spec.DomainSeparation
open Spec.FieldRepresentation Spec.SignatureComposition

theorem finishSigning_returned_iff {F Aux : Type*} [Field F]
    {lambda tau kappa higherCount : Nat}
    (prepared : Prepared F Aux lambda tau (2 ^ kappa) higherCount)
    (observation : Except (Spec.BLCRetry.Counter × Boundary lambda)
      (Spec.PartialBLCRetry.Observation lambda tau kappa))
    (signature : Signature F Aux lambda tau higherCount) :
    finishSigning prepared observation = .ok (.returned signature) ↔
      ∃ counter opening, observation = .ok (.returned counter opening) ∧
        attachOpening prepared counter opening = signature := by
  cases observation <;> simp [finishSigning, Except.map, PartialSignature.finishSigning_returned_iff]

section Signing

variable {F Aux : Type*} [Field F] [DecidableEq F]
  (category : Category) {tau kappa higherCount : Nat} (wpow : Nat)
  (prepared : Prepared F Aux (width category) tau (2 ^ kappa) higherCount)
  (Topen : Nat) (encoding : CounterEncoding) (bindings : Bindings category wpow)
  (encode : (Fin tau → Fin (2 ^ kappa)) → F) (innerFuel outerFuel : Nat)

theorem sign_returned (signature : Signature F Aux (width category) tau higherCount)
    (h : signWithBindings category wpow prepared Topen encoding bindings encode innerFuel outerFuel =
      .ok (.returned signature)) :
    ∃ counter opening challenge cursor,
      signature = attachOpening prepared counter opening ∧
      evaluateWithBindings category tau kappa wpow encoding prepared.piop counter bindings innerFuel =
        .ok (.returned challenge cursor) ∧
      Spec.BAVC.openCommitment prepared.key challenge.hidden Topen = .ok opening ∧
      Spec.BLCRetry.GrindingPassed challenge.grinding ∧ encode challenge.hidden ≠ 0 := by
  obtain ⟨counter, opening, ho, hs⟩ := (finishSigning_returned_iff prepared _ signature).mp h
  obtain ⟨_, challenge, cursor, he, hb, hg, hn⟩ := CipherBLCRetry.observe_returned
    prepared.key Topen _ encode outerFuel 0 counter opening ho
  exact ⟨counter, opening, challenge, cursor, hs.symm, he, hb, hg, hn⟩

theorem sign_returned_stable (extra : Nat)
    (signature : Signature F Aux (width category) tau higherCount)
    (h : signWithBindings category wpow prepared Topen encoding bindings encode innerFuel outerFuel =
      .ok (.returned signature)) :
    signWithBindings category wpow prepared Topen encoding bindings encode innerFuel (outerFuel + extra) =
      .ok (.returned signature) := by
  obtain ⟨counter, opening, ho, hs⟩ := (finishSigning_returned_iff prepared _ signature).mp h
  apply (finishSigning_returned_iff prepared _ signature).mpr
  exact ⟨counter, opening, CipherBLCRetry.observe_returned_stable prepared.key Topen _ encode
    outerFuel extra 0 counter opening ho, hs⟩

theorem sign_unbound_no_return (ht : 0 < tau) (hb : bindings.integerValue = none)
    (signature : Signature F Aux (width category) tau higherCount) :
    signWithBindings category wpow prepared Topen encoding bindings encode innerFuel outerFuel ≠
      .ok (.returned signature) := by
  intro h
  obtain ⟨counter, opening, ho, _⟩ := (finishSigning_returned_iff prepared _ signature).mp h
  exact CipherBLCRetry.open_unbound_no_return category tau kappa wpow ht prepared.key Topen
    encoding prepared.piop bindings hb encode innerFuel outerFuel counter opening ho

theorem signLiteral_missing :
    signLiteral category wpow prepared Topen encoding encode innerFuel (outerFuel + 1) =
      .error (0, .materialParse (readCipherMaterial category encoding prepared.piop 0)) := rfl

theorem sign_missing_integer (ht : 0 < tau) (hk : kappa ≤ 32)
    (parse : MaterialParser category) (mapping : CounterEncoding)
    (extract : Bits (width category) → Bits wpow) :
    let state := cipherAfterMaterial category mapping 0
      (parse (readCipherMaterial category encoding prepared.piop 0).value)
    let src := Spec.SHAKE.reader category (cipherInput encoding prepared.piop 0 state.ciphertexts)
    signWithBindings category wpow prepared Topen encoding
      ⟨some parse, some mapping, some extract, none⟩ encode (innerFuel + 1) (outerFuel + 1) =
      .ok (.undefinedExpansion 0 ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src)) := by
  dsimp only
  rw [signWithBindings, CipherBLCRetry.open_missing_integer category tau kappa wpow ht hk]
  rfl

end Signing

section Verification

variable {F : Type} [Field F] [DecidableEq F]
  (category : Category) {tau kappa B wit rnd higherCount : Nat} (wpow : Nat)
  (p : Spec.BLCCommit.Primitives (width category) tau kappa (width category + B) wit rnd)
  (signature : Signature F (Spec.BLCCommit.Auxiliary tau (width category + B) wit rnd)
    (width category) tau higherCount)
  (encoding : CounterEncoding) (cipherBindings : Bindings category wpow)
  (encode : (Fin tau → Fin (2 ^ kappa)) → F) (Topen : Nat)
  (blcBindings : Spec.BLCRecompute.Bindings (width category) tau kappa
    ((width category + B) + (wit + rnd)))
  (randomCount consistencyCount : Nat)
  (hrandom : (width category + B) + (wit + rnd) ≤ 8 * randomCount)
  (hconsistency : wit + rnd ≤ 8 * consistencyCount) (fuel : Nat)

theorem recompute_boundary_iff
    (state : Spec.BLCRecompute.ConsistencyBoundary F (width category) tau kappa (width category + B) wit rnd) :
    recomputeWithBindings category wpow p signature encoding cipherBindings encode Topen blcBindings
      randomCount consistencyCount hrandom hconsistency fuel = .ok (.consistencyBoundary state) ↔
      ∃ challenge cursor,
        evaluateWithBindings category tau kappa wpow encoding signature.piop signature.decomposition.1
          cipherBindings fuel = .ok (.returned challenge cursor) ∧
        Spec.BLCRecompute.prepareWithBindings p signature.salt signature.auxiliary signature.decomposition
          (fun _ => challenge) encode Topen blcBindings randomCount consistencyCount hrandom hconsistency =
          .ok state := by
  cases he : evaluateWithBindings category tau kappa wpow encoding signature.piop
      signature.decomposition.1 cipherBindings fuel with
  | error fault => simp [recomputeWithBindings, he]
  | ok observation => cases observation <;>
      simp [recomputeWithBindings, he, Spec.PartialSignature.recompute,
        PartialSignature.finishRecompute_boundary_iff]

theorem recompute_rejected_iff :
    recomputeWithBindings category wpow p signature encoding cipherBindings encode Topen blcBindings
      randomCount consistencyCount hrandom hconsistency fuel = .ok .rejected ↔
      ∃ challenge cursor,
        evaluateWithBindings category tau kappa wpow encoding signature.piop signature.decomposition.1
          cipherBindings fuel = .ok (.returned challenge cursor) ∧
        Spec.BLCRecompute.prepareWithBindings p signature.salt signature.auxiliary signature.decomposition
          (fun _ => challenge) encode Topen blcBindings randomCount consistencyCount hrandom hconsistency =
          .error .headerRejected := by
  cases he : evaluateWithBindings category tau kappa wpow encoding signature.piop
      signature.decomposition.1 cipherBindings fuel with
  | error fault => simp [recomputeWithBindings, he]
  | ok observation => cases observation <;>
      simp [recomputeWithBindings, he, Spec.PartialSignature.recompute,
        PartialSignature.finishRecompute_rejected_iff]

theorem recompute_unbound_no_boundary (ht : 0 < tau) (hb : cipherBindings.integerValue = none)
    (state : Spec.BLCRecompute.ConsistencyBoundary F (width category) tau kappa (width category + B) wit rnd) :
    recomputeWithBindings category wpow p signature encoding cipherBindings encode Topen blcBindings
      randomCount consistencyCount hrandom hconsistency fuel ≠ .ok (.consistencyBoundary state) := by
  intro h
  obtain ⟨challenge, cursor, he, _⟩ := (recompute_boundary_iff category wpow p signature encoding
    cipherBindings encode Topen blcBindings randomCount consistencyCount hrandom hconsistency fuel state).mp h
  exact CipherEvaluation.evaluate_unbound_no_return category tau kappa wpow ht encoding signature.piop
    signature.decomposition.1 cipherBindings hb fuel challenge cursor he

theorem recompute_unbound_no_rejection (ht : 0 < tau) (hb : cipherBindings.integerValue = none) :
    recomputeWithBindings category wpow p signature encoding cipherBindings encode Topen blcBindings
      randomCount consistencyCount hrandom hconsistency fuel ≠ .ok .rejected := by
  intro h
  obtain ⟨challenge, cursor, he, _⟩ := (recompute_rejected_iff category wpow p signature encoding
    cipherBindings encode Topen blcBindings randomCount consistencyCount hrandom hconsistency fuel).mp h
  exact CipherEvaluation.evaluate_unbound_no_return category tau kappa wpow ht encoding signature.piop
    signature.decomposition.1 cipherBindings hb fuel challenge cursor he

theorem recomputeLiteral_missing :
    recomputeLiteral category wpow p signature encoding encode Topen blcBindings
      randomCount consistencyCount hrandom hconsistency fuel =
      .error (.materialParse (readCipherMaterial category encoding signature.piop signature.decomposition.1)) := rfl

theorem recompute_missing_integer (ht : 0 < tau) (hk : kappa ≤ 32)
    (parse : MaterialParser category) (mapping : CounterEncoding)
    (extract : Bits (width category) → Bits wpow) :
    let state := cipherAfterMaterial category mapping signature.decomposition.1
      (parse (readCipherMaterial category encoding signature.piop signature.decomposition.1).value)
    let src := Spec.SHAKE.reader category
      (cipherInput encoding signature.piop signature.decomposition.1 state.ciphertexts)
    recomputeWithBindings category wpow p signature encoding
      ⟨some parse, some mapping, some extract, none⟩ encode Topen blcBindings
      randomCount consistencyCount hrandom hconsistency (fuel + 1) =
      .ok (.undefinedExpansion ⟨[], by simp, src⟩ (Spec.IntegerSampling.readCandidate src)) := by
  dsimp only
  rw [recomputeWithBindings, CipherEvaluation.evaluate_missing_integer category tau kappa wpow ht hk]
  rfl

end Verification

end SDitH.Proofs.CipherSignature
