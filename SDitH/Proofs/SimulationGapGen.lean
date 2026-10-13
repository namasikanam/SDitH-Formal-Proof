import SDitH.Proofs.CutHybridGen
import SDitH.Proofs.SimulationGapInv
import SDitH.Proofs.SharedGameInvariant

/-! The simulation gap under the combined invariant: the hash table
supported by the count and the shared world well formed. The
event-experiment hybrid under an abstract counted invariant takes the
global budget twice the fuel plus one. For the candidate scheme both
invariants are carried: a query keeps the shared world, the honest and
simulated signings add at most one input and run programs on the shared
world, the public oracle keeps the table and runs a program, a
programmed input keeps the shared world, and the generated keys start
with empty tables and well-formed shared worlds. So the simulation-gap
hypothesis follows from the three terms assumed only at worlds
satisfying the combined invariant at the budget. -/

namespace SDitH.Proofs.SimulationGapGen

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open ExtractionSplit (IsSolution)
open CandidateReduction ForgeryReduction SimulatedSolver
open RunHybrid RunHybridGen CutHybrid CutHybridGen EventHybrid TableSupport SimulatedWith SignCompare
open DigestFirstVsSimulated SignComparePost SimulationGap SimulationGapInv SharedGameInvariant
open scoped Classical ENNReal

noncomputable section

section Generic

variable {PublicKey SecretKey Message Signature HashInput Digest Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]
variable (sch₁ sch₂ : Scheme PublicKey SecretKey Message Signature HashInput Digest Other Query Answer)
  (adversary : Adversary PublicKey Message Signature HashInput Digest Query Answer State)
  (hagree : AgreeOffSign sch₁ sch₂) (Good : SecretKey → Prop) (eps : ℝ≥0∞) (fuel : Nat)
  (Inv : Nat → World HashInput Digest Other → Prop)
  (hmono : ∀ (n m : Nat) (world : World HashInput Digest Other), n ≤ m → Inv n world → Inv m world)
  (hquery : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat)
    (r : Digest × (HashInput → Option Digest)), Inv n world →
    r ∈ (Spec.RandomOracle.query world.hashTable input).support → Inv (n + 1) { world with hashTable := r.2 })
  (hsign : ∀ (sk : SecretKey), Good sk → ∀ (message : Message) (world : World HashInput Digest Other),
    Inv (2 * fuel + 1) world → ∀ (h : Signature × World HashInput Digest Other → PMF Bool) (c : Bool),
    ((sch₁.sign sk message world).bind h) c ≤ ((sch₂.sign sk message world).bind h) c + eps)
  (hpres₁ : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
    (r : Signature × World HashInput Digest Other), Inv n world →
    r ∈ (sch₁.sign sk message world).support → Inv (n + 1) r.2)
  (hpres₂ : ∀ (sk : SecretKey) (message : Message) (world : World HashInput Digest Other) (n : Nat)
    (r : Signature × World HashInput Digest Other), Inv n world →
    r ∈ (sch₂.sign sk message world).support → Inv (n + 1) r.2)
  (hpub : ∀ (query : Query) (world : World HashInput Digest Other) (n : Nat) (r : Answer × World HashInput Digest Other),
    Inv n world → r ∈ (sch₂.publicOracle query world).support → Inv (n + 1) r.2)
  (hupdate : ∀ (world : World HashInput Digest Other) (input : HashInput) (n : Nat) (d : Digest), Inv n world →
    Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) })

include hmono hquery hagree hsign hpres₁ hpres₂ hpub hupdate in
/-- The event-experiment hybrid under the invariant. -/
theorem eventExp_le_gen (hgood : ∀ generated ∈ sch₁.keygen.support, Good generated.2.1)
    (hkeygen : ∀ generated ∈ sch₁.keygen.support, Inv 0 generated.2.2)
    (E : Snapshot PublicKey SecretKey Message HashInput Digest Other Query State →
      Option (Branch Message Signature HashInput Digest Other Query × Branch Message Signature HashInput Digest Other Query) →
      Bool)
    (index : Nat) :
    (eventExp sch₁ adversary E index fuel) true ≤
      (eventExp sch₂ adversary E index fuel) true + (fuel * eps + 2 * fuel * eps) := by
  unfold eventExp
  refine (cutExperiment_le_gen Inv hmono hquery sch₁ sch₂ adversary hagree Good eps (2 * fuel + 1) hsign hpres₁ hpub hgood
    hkeygen index fuel (by omega) _ true).trans ?_
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
    have hsup : Inv (0 + fuel) snapshot.world :=
      cut_saved_gen Inv hmono hquery sch₂ adversary hpres₂ hpub index fuel _ _ state _ _ 0 (hkeygen generated hg₁) _ hcut
        snapshot rfl
    rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    refine (forkAt_le_gen Inv hmono hquery sch₁ sch₂ adversary hagree Good eps (2 * fuel + 1) hsign hpres₁ hpub hupdate
      snapshot hsk _ hsup (by omega) _ true).trans ?_
    exact add_le_add_right (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr hrem)) le_rfl) _

end Generic

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The combined invariant: the table supported by the count and the shared
world well formed. -/
def Inv (n : Nat)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : Prop :=
  Supported world.hashTable n ∧ WellFormed world.other

/-- The candidate services preserve well-formedness of the shared world. -/
theorem honest_preserves :
    Preserves (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) WellFormed where
  prepare := by
    intro pk sk msg other r hr hQ
    obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
    obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hroot
    have hQ' := runProgram_wellFormed _ _ other run hrun' hQ
    rw [← hres]
    cases run.1 <;> exact hQ'
  open_ := by
    intro st d other r hr hQ
    simp only [Spec.CandidateScheme.components, Spec.CandidateScheme.openSigning, PMF.mem_support_pure_iff] at hr
    subst hr
    exact hQ
  verify := by
    intro pk msg sig other r hr hQ
    change r ∈ (Spec.CandidateScheme.prepareVerification S V verifyBudget pk msg sig other).support at hr
    unfold Spec.CandidateScheme.prepareVerification at hr
    rcases hbody : sig.body with _ | body
    · rw [hbody] at hr
      simp only [PMF.mem_support_pure_iff] at hr
      subst hr
      exact hQ
    · rw [hbody] at hr
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact runProgram_wellFormed _ _ other run hrun' hQ
  oracle := by
    intro q other r hr hQ
    cases q with
    | hash input =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact runProgram_wellFormed _ _ other run hrun' hQ
    | mask input =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact runProgram_wellFormed _ _ other run hrun' hQ
    | cipher request =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact runProgram_wellFormed _ _ other run hrun' hQ

/-- The simulated signing's shared world is a commitment run's world. -/
theorem simulatedSign_other (message : List Bool)
    (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
      (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (r) (hr : r ∈ (simulatedSign S publicKey message world).support) : WellFormed world.other → WellFormed r.2.other := by
  intro hw
  obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
  obtain ⟨fake, _, hfake⟩ := (PMF.mem_support_bind_iff _ _ _).mp hroot
  obtain ⟨digest, _, hdigest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hfake
  obtain ⟨run, hrun, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hdigest
  have hw' := runProgram_wellFormed _ _ world.other run hrun hw
  rw [← hres]
  dsimp only
  split <;> (try split) <;> (try split) <;> exact hw'

omit [Field F] [Algebra (ZMod 2) F] [DecidableEq F] in
theorem inv_mono (n m : Nat) (world) (hnm : n ≤ m) (h : Inv (lambda := lambda) (s := s) (higherCount := higherCount)
    (w := w) (widths := widths) (F := F) n world) : Inv m world :=
  ⟨supported_mono h.1 hnm, h.2⟩

omit [Field F] [Algebra (ZMod 2) F] [DecidableEq F] in
theorem inv_query (world) (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (n : Nat)
    (r : Spec.BAVC.Digest lambda × (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) →
      Option (Spec.BAVC.Digest lambda)))
    (h : Inv (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) n world)
    (hr : r ∈ (Spec.RandomOracle.query world.hashTable input).support) : Inv (n + 1) { world with hashTable := r.2 } :=
  ⟨supported_query h.1 input r hr, h.2⟩

omit [Field F] [Algebra (ZMod 2) F] [DecidableEq F] in
theorem inv_update (world) (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (n : Nat)
    (d : Spec.BAVC.Digest lambda)
    (h : Inv (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) n world) :
    Inv (n + 1) { world with hashTable := Function.update world.hashTable input (some d) } :=
  ⟨supported_update h.1 input d, h.2⟩

/-- The candidate scheme's public oracle advances the invariant count. -/
theorem inv_pub (query : Query lambda) (world) (n : Nat) (r)
    (h : Inv (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) n world)
    (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).publicOracle query world).support) :
    Inv (n + 1) r.2 := by
  refine ⟨?_, ?_⟩
  · rw [publicOracle_table S V verifyBudget publicKey sampleWitness query world r hr]
    exact supported_mono h.1 (Nat.le_succ n)
  · exact oracle_preserves (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) WellFormed
      (honest_preserves S V verifyBudget publicKey sampleWitness) query world r hr h.2

/-- The generated keys satisfy the invariant at zero. -/
theorem inv_keygen :
    ∀ generated ∈ (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).keygen.support,
      Inv (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) 0 generated.2.2 := by
  intro generated hg
  obtain ⟨g, hg', rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hg
  exact ⟨supported_empty 0, keygen_wellFormed publicKey sampleWitness g hg'⟩

/-- The honest signing grows the invariant count by one. -/
theorem inv_honest (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) (world) (n : Nat) (r)
    (h : Inv (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) n world)
    (hr : r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message
      world).support) : Inv (n + 1) r.2 :=
  ⟨honest_pres S V verifyBudget publicKey sampleWitness sk message world n r h.1 hr,
    sign_preserves (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness) WellFormed
      (honest_preserves S V verifyBudget publicKey sampleWitness) sk message world r hr h.2⟩

/-- The simulated signing grows the invariant count by one. -/
theorem inv_simulated (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) (world) (n : Nat) (r)
    (h : Inv (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) n world)
    (hr : r ∈ ((simulatedScheme S V verifyBudget publicKey sampleWitness).sign sk message world).support) : Inv (n + 1) r.2 :=
  ⟨simulatedSign_supported S sk.1 message world h.1 r hr, simulatedSign_other S sk.1 message world r hr h.2⟩

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The simulation gap with the per-call terms assumed only at worlds
satisfying the combined invariant at twice the fuel plus three. -/
theorem hgap_of_uniform_gen (hpc : PayloadConsistent S)
    (hsample : ∀ witness ∈ sampleWitness.support, IsSolution S witness) (εP εR εS : ℝ≥0∞) (fuel : Nat)
    (hpresent : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      Inv (2 * (fuel + 1) + 1) world → (inputPresent S publicKey witness message world) true ≤ εP)
    (hretry : ∀ (witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      Inv (2 * (fuel + 1) + 1) world → (retryEvent S publicKey witness message world) true ≤ εR)
    (hswap : ∀ (witness fake : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
      Inv (2 * (fuel + 1) + 1) world →
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
      Inv (2 * (fuel + 1) + 1) world →
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
  unfold randomEventExperiment simEventExperiment
  refine bind_le_bind_add_const' _ _ _ _ true (fun index _ => ?_)
  have hev := eventExp_le_gen (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary (agree S V verifyBudget publicKey sampleWitness)
    (GoodKey S publicKey) (εP + εR + εS) (fuel + 1) Inv inv_mono inv_query hsign
    (inv_honest S V verifyBudget publicKey sampleWitness) (inv_simulated S V verifyBudget publicKey sampleWitness)
    (inv_pub S V verifyBudget publicKey sampleWitness) inv_update
    (keygen_good S V verifyBudget publicKey sampleWitness hsample) (inv_keygen S V verifyBudget publicKey sampleWitness)
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
end SDitH.Proofs.SimulationGapGen
