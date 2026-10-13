import SDitH.Proofs.TouchIdentity
import SDitH.Proofs.SimulationGapCompat

/-! The touching bounds of the swap discharge from the touching total: the
swap's touching term is the touching total's probability; the total is
bounded uniformly through the history's length, which the extended
invariant bounds by the commitment budget times the count; the expected
recorded length is bounded by the end budget; the leaf term remains a
named hypothesis. -/

namespace SDitH.Proofs.TouchBound

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator Spec.BLC
open Spec.SharedSigner (commitBudget Committed)
open Spec.BAVC (Digest)
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher (Family Entry)
open Spec.RandomOracleTrap (indicator)
open Spec.SlopeConsistencyGame (Out)
open CandidateResample CipherInvariant HiddenEntries GamePrune SignBridge SwapDischarge SharedPrune HiddenTuple HiddenSlice
open GameResample CipherResample ChargeExpect ChargeCutExpect TouchSplit TouchAssembly TouchTotal RootPosteriorBound
open CommitViewExchange ForkOutcome TouchPrep TouchIdentity SimulationGapCompat MeanHybridCompat MeanCutCompat CutWorld
open RunWorld MeanForkCont TreeStepFresh CandidatePrepLaw InvCExtra
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

/-- The uniform touching bound: the touching total's bound with the
history's key count replaced by the budget, the expected recorded length
by the commitment budget times the end budget, and the leaf term by its
bound. -/
def εTouch (c cKey M B' : Nat) (εLeaf : ℝ≥0∞) : ℝ≥0∞ :=
  (((cKey * M : Nat) : ℝ≥0∞) * (Fintype.card (Bits lambda) : ℝ≥0∞)⁻¹ +
    (tau * 2 ^ kappa - 1 : ℕ) *
      (2 * (((c * (M + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) /
          ((Fintype.card (Bits lambda) - (M + 2 * (tau * 2 ^ kappa - 1) + 1) : Nat) : ℝ≥0∞)) +
        (c : ℝ≥0∞) / ((Fintype.card (Bits lambda) - (M + 2 * (tau * 2 ^ kappa - 1) + 1) : Nat) : ℝ≥0∞))) +
  ((tau : ℝ≥0∞) *
      ((cKey : ℝ≥0∞) / ((Fintype.card (Bits lambda) - cKey * (M + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) +
        (Nat.log 2 (tau * 2 ^ kappa) : ℝ≥0∞) * ((c : ℝ≥0∞) /
          ((Fintype.card (Bits lambda) - (c * (M + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞))) *
      ((commitBudget tau kappa * B' : Nat) : ℝ≥0∞) +
    εLeaf)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A history's key count is at most its length. -/
theorem card_keysOf_le (H : List (Entry (Bits lambda) (Bits lambda))) : (keysOf H).card ≤ H.length := by
  unfold keysOf
  exact (List.toFinset_card_le _).trans (by rw [List.length_map])

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A pair of the joint draw has a family from the posterior. -/
theorem mem_rootDraw (H₀ : List (Entry (Bits lambda) (Bits lambda))) (x : Bits lambda × Family (Bits lambda) (Bits lambda))
    (hx : x ∈ (rootDraw H₀).support) : x.2 ∈ (posterior H₀).support := by
  unfold rootDraw ProductSwap.product at hx
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hx
  obtain ⟨r, -, g, hg, rfl⟩ := hx
  exact hg

variable (Gc : Signature (Digest lambda)
    (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) →
  GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
    (selectorCount widths * w) (lambda * (widths.length - 1)) →
  PMF (GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
    (selectorCount widths * w) (lambda * (widths.length - 1))))

include V verifyBudget sampleWitness in
/-- The swap's touching term is at most the uniform touching bound, for a
game process keeping the invariant to the end budget and a bounded leaf
term. -/
theorem touchMean_le (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (B B' m : Nat) (hmB : m ≤ B)
    (hNb : c * (commitBudget tau kappa * B + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * B + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hw : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) m world)
    (hGc : ∀ sig w'', InvC (tau := tau) (kappa := kappa) (m + 1) w'' → ∀ y ∈ (Gc sig w'').support,
      InvC (tau := tau) (kappa := kappa) B' y)
    (εLeaf : ℝ≥0∞)
    (hleaf : ∀ (salt : Bits lambda) (digest : Digest lambda),
      leafTerm S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc)
        newT ≤ εLeaf) :
    touchMean S publicKey (sigHidden S) wsign message world (fun K r => mean (Gc r.1 r.2) fun y => indicator (touchesG K y)) ≤
      εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B) B' εLeaf := by
  have hpos : ∃ g : Family (Bits lambda) (Bits lambda), Spec.IdealCipher.Matches g world.other.cipherHistory := ⟨_, hw.2.1⟩
  have hlen : world.other.cipherHistory.length ≤ commitBudget tau kappa * B :=
    hw.2.2.trans (Nat.mul_le_mul_left _ hmB)
  have hcard : (keysOf world.other.cipherHistory).card ≤ commitBudget tau kappa * B :=
    (card_keysOf_le _).trans hlen
  have hNb' : c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda) :=
    lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _) hNb
  have hNR' : cKey * ((keysOf world.other.cipherHistory).card + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hNR
  unfold touchMean
  refine mean_le_const _ _ _ fun salt _ => ?_
  rw [mean_comm]
  refine mean_le_const _ _ _ fun digest _ => ?_
  rw [touchInner_eq_touchAll S publicKey Gc wsign message salt digest world]
  have htt := touch_total S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S)
    (contT Gc) newT hL2 hin hl hL (fun b hb c x => simPost_setTree S publicKey message salt digest b hb x c world.hashTable) hpos
    c hfiber cKey hfiberR hNb' hNR' (commitBudget tau kappa * B + 2 * (tau * 2 ^ kappa - 1) + 1) (by omega)
  refine htt.trans ?_
  have hE : mean (rootDraw world.other.cipherHistory)
      (expLen S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc) newT) ≤
      ((commitBudget tau kappa * B' : Nat) : ℝ≥0∞) :=
    mean_le_const _ _ _ fun x hx => by
      have := expLen_le S publicKey Gc V verifyBudget sampleWitness wsign message salt digest m B' world hw hGc x
        (PrunedRun.matches_of_mem_posterior _ hpos x.2 (mem_rootDraw _ x hx))
      exact_mod_cast this
  unfold εTouch
  have hA1 : ((cKey * (keysOf world.other.cipherHistory).card : Nat) : ℝ≥0∞) ≤ ((cKey * (commitBudget tau kappa * B) : Nat) : ℝ≥0∞) :=
    Nat.cast_le.mpr (Nat.mul_le_mul_left _ hcard)
  have hA2 : ((c * ((keysOf world.other.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) ≤
      ((c * (commitBudget tau kappa * B + 2 * (tau * 2 ^ kappa)) : Nat) : ℝ≥0∞) :=
    Nat.cast_le.mpr (Nat.mul_le_mul_left _ (by omega))
  have hD1 : ((Fintype.card (Bits lambda) - cKey * (commitBudget tau kappa * B + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card (Bits lambda) - cKey * ((keysOf world.other.cipherHistory).card + 2 * (tau * 2 ^ kappa)) : ℕ) : ℝ≥0∞) :=
    Nat.cast_le.mpr (Nat.sub_le_sub_left (Nat.mul_le_mul_left _ (by omega)) _)
  have hD2 : ((Fintype.card (Bits lambda) - (c * (commitBudget tau kappa * B + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card (Bits lambda) - (c * ((keysOf world.other.cipherHistory).card + 1 + 2 * (tau * 2 ^ kappa)) + 1) : ℕ) : ℝ≥0∞) :=
    Nat.cast_le.mpr (Nat.sub_le_sub_left (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _) _)
  refine add_le_add (add_le_add (mul_le_mul' hA1 le_rfl) (mul_le_mul' le_rfl (add_le_add
    (mul_le_mul' le_rfl (ENNReal.div_le_div_right hA2 _)) le_rfl))) (add_le_add (mul_le_mul' (mul_le_mul' le_rfl (add_le_add
    (ENNReal.div_le_div_left hD1 _) (mul_le_mul' le_rfl (ENNReal.div_le_div_left hD2 _)))) hE) (hleaf salt digest))

variable {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The extended invariant along the simulated scheme's cut with its final
world. -/
theorem cutW_inv_sim (hvc : verifyBudget ≤ commitBudget tau kappa) :
    ∀ (index fuel : Nat) (pk : List Bool) (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (state : State)
      (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
      (n : Nat), InvC (tau := tau) (kappa := kappa) n world →
      ∀ r ∈ (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel pk sk state world trace).support,
        InvC (tau := tau) (kappa := kappa) (n + fuel) r.2 := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace n hn r hr
    simp only [cutW, PMF.support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simpa using hn
  | succ fuel ih =>
    intro pk sk state world trace n hn r hr
    simp only [cutW, PMF.mem_support_bind_iff] at hr
    obtain ⟨action, -, hr⟩ := hr
    cases action with
    | abort =>
      simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact invC_mono _ _ _ (by omega) hn
    | finish message signature =>
      simp only [PMF.support_map, Set.mem_image] at hr
      obtain ⟨result, hres', rfl⟩ := hr
      exact invC_mono _ _ _ (by omega) (invC_prep S V verifyBudget publicKey sampleWitness hvc pk message signature world n result hn hres')
    | sign message next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres', hr⟩ := hr
      exact invC_mono _ _ _ (by omega)
        (ih index pk sk _ _ _ (n + 1) (invC_simulated S V verifyBudget publicKey sampleWitness sk message world n result hn hres') r hr)
    | hash input next =>
      cases index with
      | zero =>
        simp only [PMF.support_pure, Set.mem_singleton_iff] at hr
        subst hr
        exact invC_mono _ _ _ (by omega) hn
      | succ index =>
        simp only [PMF.mem_support_bind_iff] at hr
        obtain ⟨result, hres', hr⟩ := hr
        exact invC_mono _ _ _ (by omega) (ih index pk sk _ _ _ (n + 1) (invC_query world input n result hn hres') r hr)
    | query input next =>
      simp only [PMF.mem_support_bind_iff] at hr
      obtain ⟨result, hres', hr⟩ := hr
      exact invC_mono _ _ _ (by omega)
        (ih index pk sk _ _ _ (n + 1) (invC_pub S V verifyBudget publicKey sampleWitness input world n result hn hres') r hr)

/-- The leaf-term bound for the run's continuations: a named hypothesis. -/
def LeafR (εLeaf : ℝ≥0∞) (B : Nat) : Prop :=
  ∀ (wsign witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (m : Nat) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
    InvC (tau := tau) (kappa := kappa) m world →
    ∀ (fuel' : Nat) (pk : List Bool) (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
      (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
      (Cp : Terminal (List Bool) (Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) → PMF (Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))),
      m + fuel' + 1 ≤ B → ∀ (salt : Bits lambda) (digest : Digest lambda),
      leafTerm S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S)
        (contT (fun sig w'' => (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk
          (publicKey, witness) (next sig) w'' trace).bind Cp)) newT ≤ εLeaf

/-- The leaf-term bound for the cut's continuations: a named hypothesis. -/
def LeafC (εLeaf : ℝ≥0∞) (B : Nat) : Prop :=
  ∀ (wsign witness : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (m : Nat) (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))),
    InvC (tau := tau) (kappa := kappa) m world →
    ∀ (index fuel' : Nat) (pk : List Bool) (next : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) → State)
      (trace : Trace (List Bool) (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Query lambda))
      (Cp : Cut (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool) (Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
        (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
        (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) →
        PMF (Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))),
      m + fuel' + 1 ≤ B → ∀ (salt : Bits lambda) (digest : Digest lambda),
      leafTerm S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S)
        (contT (fun sig w'' => (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk
          (publicKey, witness) (next sig) w'' trace).bind Cp)) newT ≤ εLeaf

/-- The touching bound for the run's continuations, from the touching total. -/
theorem touchR_of (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (B B' : Nat)
    (hNb : c * (commitBudget tau kappa * B + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * B + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (εLeaf : ℝ≥0∞) (hleaf : LeafR S V verifyBudget publicKey sampleWitness adversary εLeaf B) :
    TouchR S V verifyBudget publicKey sampleWitness adversary
      (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B) B' εLeaf) B B' := by
  intro wsign witness message m world hw fuel' hfuel pk next trace Cp hCp
  have heq : (fun (K : List (Bits lambda)) (r : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) =>
      mean (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness) (next r.1) r.2
        trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) =
      fun K r => mean ((runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness)
        (next r.1) r.2 trace).bind Cp) fun y => indicator (touchesG K y) := by
    funext K r
    rw [mean_bind]
  rw [heq]
  refine touchMean_le S V verifyBudget publicKey sampleWitness
    (fun sig w'' => (runW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary fuel' pk (publicKey, witness)
      (next sig) w'' trace).bind Cp) hL2 hin hl hL c hfiber cKey hfiberR B B' m (by omega) hNb hNR wsign message world hw ?_ εLeaf
    (hleaf wsign witness message m world hw fuel' pk next trace Cp hfuel)
  intro sig w'' hw'' y hy
  obtain ⟨t, ht, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
  have h := runW_inv (simulatedScheme S V verifyBudget publicKey sampleWitness)
    (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary ⟨rfl, rfl, rfl, rfl⟩ (InvC (tau := tau) (kappa := kappa))
    invC_mono invC_query (invC_simulated S V verifyBudget publicKey sampleWitness) (invC_pub S V verifyBudget publicKey sampleWitness)
    (invC_prep S V verifyBudget publicKey sampleWitness hvc) fuel' pk _ (next sig) w'' trace (m + 1) hw'' t ht
  exact hCp t (invC_mono _ _ _ (by omega) h) y hy

/-- The touching bound for the cut's continuations, from the touching total. -/
theorem touchC_of (hL2 : 2 ≤ tau * 2 ^ kappa) (hin : Function.Injective S.signer.layout.input) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (c : Nat) (hfiber : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key (S.signer.layout.output r) = κ} ≤ c)
    (cKey : Nat) (hfiberR : ∀ κ, Fintype.card {r : Bits lambda // S.signer.layout.key r = κ} ≤ cKey)
    (hvc : verifyBudget ≤ commitBudget tau kappa) (B B' : Nat)
    (hNb : c * (commitBudget tau kappa * B + 1 + 2 * (tau * 2 ^ kappa)) + 1 < Fintype.card (Bits lambda))
    (hNR : cKey * (commitBudget tau kappa * B + 2 * (tau * 2 ^ kappa)) < Fintype.card (Bits lambda))
    (εLeaf : ℝ≥0∞) (hleaf : LeafC S V verifyBudget publicKey sampleWitness adversary εLeaf B) :
    TouchC S V verifyBudget publicKey sampleWitness adversary
      (εTouch (lambda := lambda) (tau := tau) (kappa := kappa) c cKey (commitBudget tau kappa * B) B' εLeaf) B B' := by
  intro wsign witness message m world hw index fuel' hfuel pk next trace Cp hCp
  have heq : (fun (K : List (Bits lambda)) (r : Signature (Spec.BAVC.Digest lambda)
          (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) × Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) =>
      mean (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness) (next r.1)
        r.2 trace) fun t => mean (Cp t) fun y => indicator (touchesG K y)) =
      fun K r => mean ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
        (next r.1) r.2 trace).bind Cp) fun y => indicator (touchesG K y) := by
    funext K r
    rw [mean_bind]
  rw [heq]
  refine touchMean_le S V verifyBudget publicKey sampleWitness
    (fun sig w'' => (cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
      (next sig) w'' trace).bind Cp) hL2 hin hl hL c hfiber cKey hfiberR B B' m (by omega) hNb hNR wsign message world hw ?_ εLeaf
    (hleaf wsign witness message m world hw index fuel' pk next trace Cp hfuel)
  intro sig w'' hw'' y hy
  obtain ⟨t, ht, hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
  have h := cutW_inv_sim S V verifyBudget publicKey sampleWitness adversary hvc index fuel' pk _ (next sig) w'' trace (m + 1) hw''
    t ht
  have hreach : ReachC B t.1 := by
    intro sn hsn
    have hmem : t.1 ∈ ((cutW (simulatedScheme S V verifyBudget publicKey sampleWitness) adversary index fuel' pk (publicKey, witness)
        (next sig) w'' trace).map Prod.fst).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩
    rw [cutW_fst] at hmem
    exact (ForkEventUnion.cut_remaining_le _ adversary index fuel' pk _ (next sig) w'' trace t.1 hmem sn hsn).trans (by omega)
  exact hCp t (invC_mono _ _ _ (by omega) h) hreach y hy

end
end SDitH.Proofs.TouchBound
