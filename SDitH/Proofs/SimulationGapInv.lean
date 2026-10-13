import SDitH.Proofs.CutHybridInv
import SDitH.Proofs.SimulationGap

/-! The simulation gap with the per-call terms at supported worlds only.
The event-experiment hybrid under the table-support invariant takes the
global budget twice the fuel plus one (the cut's support plus one
programmed input plus the remaining fuel). For the candidate scheme the
honest signing adds at most one input for good keys, the simulated
signing adds at most one, the public oracle keeps the table and the
generated keys start with empty tables; so the simulation-gap hypothesis
follows from uniform bounds on the input-present event, the
retry-failure event and the witness-swap term assumed only at worlds
supported by the budget. -/

namespace SDitH.Proofs.SimulationGapInv

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction SimulatedSolver
open RunHybrid RunHybridInv CutHybrid CutHybridInv EventHybrid TableSupport SimulatedWith SignCompare
open DigestFirstVsSimulated SignComparePost SimulationGap
open scoped Classical ENNReal

noncomputable section

section Generic

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : ℝ≥0∞) (fuel : Nat)
  (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
    Supported world.hashTable (2 * fuel + 1) → ∀ (h : Signature × World HashInput Digest Other → PMF Bool) (c : Bool),
    ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps)
  (hpres₁ : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
    (r : Signature × World HashInput Digest Other), Supported world.hashTable n →
    r ∈ (sch₁.sign sk message world).support → Supported r.2.hashTable (n + 1))
  (hpres₂ : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
    (r : Signature × World HashInput Digest Other), Supported world.hashTable n →
    r ∈ (sch₂.sign sk message world).support → Supported r.2.hashTable (n + 1))
  (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (r : Answer × World HashInput Digest Other),
    r ∈ (sch₂.publicOracle query world).support → r.2.hashTable = world.hashTable)

include hagree hsign hpres₁ hpres₂ hpub in
/-- The event-experiment hybrid under the invariant. -/
theorem eventExp_le_inv (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1)
    (hkeygen : ∀ generated ∈ sch₁.keygen.support, Supported generated.2.2.hashTable 0)
    (E : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State →
      Option (Branch Message Signature HashInput Digest Other Query × Branch Message Signature HashInput Digest Other Query) →
      Bool)
    (index : Nat) :
    (eventExp sch₁ adversary E index fuel) true ≤
      (eventExp sch₂ adversary E index fuel) true + (fuel * eps + 2 * fuel * eps) := by
  unfold eventExp
  refine (cutExperiment_le_inv sch₁ sch₂ adversary hagree Good eps (2 * fuel + 1) hsign hpres₁ hpub hgood hkeygen index
    fuel (by omega) _ true).trans ?_
  rw [add_comm (fuel * eps) (2 * fuel * eps), ← add_assoc]
  refine add_le_add_left ?_ _
  refine bind_le_bind_add_const' _ _ _ _ true (fun c hc => ?_)
  cases c with
  | ended t =>
    dsimp only
    exact le_self_add
  | saved snapshot =>
    dsimp only
    obtain ⟨generated, hg, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
    obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
    have hg₁ : generated ∈ sch₁.keygen.support := by rw [hagree.keygen]; exact hg
    have hrem : snapshot.remaining ≤ fuel :=
      ForkEventUnion.cut_remaining_le sch₂ adversary index fuel _ _ state _ _ _ hcut snapshot rfl
    have hkey : snapshot.secretKey = generated.2.1 :=
      cut_saved_secretKey sch₂ adversary index fuel _ _ state _ _ _ hcut snapshot rfl
    have hsk : Good snapshot.secretKey := by
      rw [hkey]
      exact hgood generated hg₁
    have hsup : Supported snapshot.world.hashTable (0 + fuel) :=
      cut_saved_supported sch₂ adversary hpres₂ hpub index fuel _ _ state _ _ 0 (hkeygen generated hg₁) _ hcut snapshot rfl
    rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    refine (forkAt_le_inv sch₁ sch₂ adversary hagree Good eps (2 * fuel + 1) hsign hpres₁ hpub snapshot hsk _ hsup
      (by omega) _ true).trans ?_
    exact add_le_add_right (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr hrem)) le_rfl) _

end Generic

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The candidate scheme's public oracle keeps the hash table. -/
theorem publicOracle_table (query : Query lambda)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (r) (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).publicOracle query world).support) :
    r.2.hashTable = world.hashTable := by
  obtain ⟨result, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  rfl

/-- The generated keys start with empty hash tables. -/
theorem keygen_table :
    ∀ generated ∈ (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).keygen.support,
      Supported generated.2.2.hashTable 0 := by
  intro generated hg
  obtain ⟨g, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
  exact supported_empty 0

/-- The honest scheme's signing at any public key component: salt, root, the
commitment run, the PIOP hash query at the prepared payload, and the
opening. -/
theorem honest_sign_eq' (pk' : List Bool) (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign (pk', witness) message world =
      (PMF.uniformOfFintype (Bits lambda)).bind fun salt =>
        (PMF.uniformOfFintype (Bits lambda)).bind fun root =>
          (runProgram (commitBudget tau kappa) (commitProgram S.signer salt root witness) world.other).bind fun result =>
            (Spec.RandomOracle.query world.hashTable
              (⟨pk', message, (SignStep.preparedOf S salt result).1⟩ :
                HashInput (List Bool) (List Bool) (Payload F lambda higherCount))).bind fun hashResult =>
                (Spec.CandidateScheme.openSigning S (SignStep.preparedOf S salt result).2.1 hashResult.1
                  (SignStep.preparedOf S salt result).2.2).map
                  fun opened => (⟨hashResult.1, opened.1⟩, ⟨hashResult.2, opened.2⟩) := by
  show (prepareSigning S pk' witness message world.other).bind _ = _
  rw [SignStep.prepareSigning_eq]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl

/-- The honest signing adds at most one input, for every secret key. -/
theorem honest_pres (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (n : Nat)
    (r) (hn : Supported world.hashTable n)
    (hr : r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message
      world).support) :
    Supported r.2.hashTable (n + 1) := by
  rcases sk with ⟨pk', witness⟩
  rw [honest_sign_eq'] at hr
  obtain ⟨salt, _, h1⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, h2⟩ := (PMF.mem_support_bind_iff _ _ _).mp h1
  obtain ⟨res, _, h3⟩ := (PMF.mem_support_bind_iff _ _ _).mp h2
  obtain ⟨hashResult, hq, h4⟩ := (PMF.mem_support_bind_iff _ _ _).mp h3
  obtain ⟨opened, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp h4
  subst heq
  exact supported_query hn _ hashResult hq

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The simulation gap with the per-call terms assumed only at worlds
supported by twice the fuel plus three. -/
theorem hgap_of_uniform_inv (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (εP εR εS : ℝ≥0∞) (fuel : Nat)
    (hpresent : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      Supported world.hashTable (2 * (fuel + 1) + 1) → (inputPresent S publicKey witness message world) true ≤ εP)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      Supported world.hashTable (2 * (fuel + 1) + 1) → (retryEvent S publicKey witness message world) true ≤ εR)
    (hswap : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      Supported world.hashTable (2 * (fuel + 1) + 1) →
      ∀ (h : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
        Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
          (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
      (c : Bool),
      ((simulatedSignWith S publicKey witness message world).bind h) c ≤
        ((simulatedSignWith S publicKey fake message world).bind h) c + εS)
    (E : Snap F lambda s higherCount w widths State →
      Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary E fuel) true ≤
      (simEventExperiment adversary (simulatedScheme S V verifyBudget publicKey sampleWitness) E fuel) true +
        3 * ((fuel : ℝ≥0∞) + 1) * (εP + εR + εS) := by
  have hsign : ∀ sk, GoodKey S publicKey sk → ∀ (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      Supported world.hashTable (2 * (fuel + 1) + 1) →
      ∀ (h : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
        Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
          (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF Bool)
      (c : Bool),
      (((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message world).bind h) c ≤
        (((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message world).bind h) c + (εP + εR + εS) := by
    intro sk hsk message world hw h c
    obtain ⟨hpk, hsol⟩ := hsk
    rcases sk with ⟨pk', witness⟩
    dsimp only at hpk hsol
    subst hpk
    refine (honest_le_simulated_post S V verifyBudget _ sampleWitness hpc witness hsol message world h εS
      (fun fake c' => hswap witness fake message world hw h c') c).trans ?_
    exact add_le_add_right (add_le_add (add_le_add (hpresent witness message world hw) (hretry witness message world hw))
      le_rfl) _
  have hpres₂ : ∀ (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (n : Nat) r,
      Supported world.hashTable n →
      r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message world).support →
      Supported r.2.hashTable (n + 1) :=
    fun sk message world n r hn hr => simulatedSign_supported S sk.1 message world hn r hr
  unfold randomEventExperiment simEventExperiment
  refine bind_le_bind_add_const' _ _ _ _ true (fun index _ => ?_)
  have hev := eventExp_le_inv (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (agree S V verifyBudget publicKey sampleWitness)
    (GoodKey S publicKey) (εP + εR + εS) (fuel + 1) hsign
    (honest_pres S V verifyBudget publicKey sampleWitness)
    hpres₂ (publicOracle_table S V verifyBudget publicKey sampleWitness)
    (keygen_good S V verifyBudget publicKey sampleWitness hsample) (keygen_table S V verifyBudget publicKey sampleWitness)
    E index.val
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
end SDitH.Proofs.SimulationGapInv
