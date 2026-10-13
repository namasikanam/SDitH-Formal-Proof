import SDitH.Proofs.EventHybrid
import SDitH.Proofs.SignComparePost

/-! The simulation gap of the composed bound. The candidate scheme and the
witness-free simulated scheme agree off signing; the game's generated
keys carry the public key with a solution witness; for such keys the
per-signature comparison gives a per-call bound under continuations
from uniform bounds on the input-present and retry-failure events and
the witness-swap term. The event-experiment hybrid then bounds the
random-index event experiments: the honest one is within three times the
fuel plus one times the per-call bound of the simulated one, which is
the simulation-gap hypothesis of the composed forgery bound. -/

namespace SDitH.Proofs.SimulationGap

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction SimulatedSolver
open RunHybrid CutHybrid EventHybrid SimulatedWith SignCompare DigestFirstVsSimulated SignComparePost
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The candidate scheme and the simulated scheme agree off signing. -/
theorem agree :
    AgreeOffSign (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      (simulatedScheme S V verifyBudget publicKey sampleWitness) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Good secret keys: the game's public key with a solution witness. -/
def GoodKey (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) : Prop :=
  sk.1 = publicKey ∧ IsSolution S sk.2

/-- The game's generated keys are good when the witness sampler yields
solutions. -/
theorem keygen_good (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) :
    ∀ generated ∈ (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).keygen.support,
      GoodKey S publicKey generated.2.1 := by
  intro generated hg
  obtain ⟨g, hg', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
  obtain ⟨witness, hw, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg'
  obtain ⟨family, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  exact ⟨rfl, hsample witness hw⟩

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The simulation gap from uniform per-call bounds: the honest random-index
event experiment is within three times the fuel plus one times the
per-call bound of the simulated one. -/
theorem hgap_of_uniform (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (εP εR εS : ℝ≥0∞)
    (hpresent : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      (inputPresent S publicKey witness message world) true ≤ εP)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      (retryEvent S publicKey witness message world) true ≤ εR)
    (hswap : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
      (h : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
        Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
          (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
      (c : Bool),
      ((simulatedSignWith S publicKey witness message world).bind h) c ≤
        ((simulatedSignWith S publicKey fake message world).bind h) c + εS)
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool)
    (fuel : Nat) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        3 * ((fuel : ℝ≥0∞) + 1) * (εP + εR + εS) := by
  have hsign : ∀ sk, GoodKey S publicKey sk → ∀ (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
      (h : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
        Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
          (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
      (c : Bool),
      (((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message world).bind h) c ≤
        (((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message world).bind h) c + (εP + εR + εS) := by
    intro sk hsk message world h c
    obtain ⟨hpk, hsol⟩ := hsk
    rcases sk with ⟨pk', witness⟩
    dsimp only at hpk hsol
    subst hpk
    refine (honest_le_simulated_post S V verifyBudget _ sampleWitness hpc witness hsol message world h εS
      (fun fake c' => hswap witness fake message world h c') c).trans ?_
    exact add_le_add_right (add_le_add (add_le_add (hpresent witness message world) (hretry witness message world)) le_rfl) _
  unfold randomEventExperiment simEventExperiment
  refine bind_le_bind_add_const' _ _ _ _ true (fun index _ => ?_)
  have hev := eventExp_le (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (agree S V verifyBudget publicKey sampleWitness)
    (GoodKey S publicKey) (εP + εR + εS) hsign (keygen_good S V verifyBudget publicKey sampleWitness hsample) E index.val
    (fuel + 1)
  have heq₁ : eventExperiment S V verifyBudget publicKey sampleWitness adversary E index.val (fuel + 1) =
      eventExp (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary E index.val
        (fuel + 1) := by
    unfold eventExperiment eventExp
    first
      | rfl
      | (congr 1; funext c; cases c <;> rfl)
  rw [heq₁]
  refine hev.trans (le_of_eq ?_)
  congr 1 <;> first
    | rfl
    | (unfold eventExp; congr 1; congr 1; funext c; cases c <;> rfl)
    | (unfold eventExp)
    | (push_cast; ring1)

end
end SDitH.Proofs.SimulationGap
