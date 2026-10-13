import SDitH.Proofs.SeedCollisionWitness
import SDitH.Proofs.CandidateKeepsFamily
import SDitH.Proofs.CandidateShift
import SDitH.Proofs.SimulationGap
import SDitH.Proofs.ForkEventUnion
import SDitH.Proofs.CutHybridGen
import SDitH.Proofs.ForgeryReduction

/-! The seed-collision bound: the real experiment's probability of the
seed-collision event is at most three times the fuel plus one, times one
call's pair cost at the counted invariant's largest history length. The
cut run and the two fork branches each spend at most the fuel plus one
calls, the fork's event is bounded by the second branch's pair mass, and
the key generation's history is empty. -/

namespace SDitH.Proofs.SeedCollisionBound

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.SignatureReplay Spec.AbstractSignature
open Spec.HashCipherProgram Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator
open Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher Spec.IdealCipherPairCollision
open CipherResample GameResample ChargeExpect SharedResample CandidateResample CandidatePrepLaw
open GamePrune PruneLawRun CandidatePrune CipherInvariant InvCExtra CandidateReduction CandidateKeepsFamily CandidateShift
open SimulationGap ChargeCutExpect CutHybridGen ForkEventUnion MeanHybrid HiddenSlice
open PairMass PairOracles PairRun PairFork SeedCollisionWitness ForgeryReduction
open scoped Classical ENNReal

noncomputable section

theorem callCost_mono_len (lambda capacity b : Nat) {L L' : Nat} (h : L ≤ L') :
    callCost lambda capacity L b ≤ callCost lambda capacity L' b := by
  unfold callCost
  refine mul_le_mul' (Nat.cast_le.mpr ?_) (pairCost_mono _ (by omega))
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h) le_rfl

/-- The seed-collision slack: three times the fuel plus one, times one call's
pair cost at the largest history length. -/
def εCollOf (lambda tau kappa cOut fuel : Nat) : ℝ≥0∞ :=
  ((3 * (fuel + 1) : Nat) : ℝ≥0∞) *
    callCost lambda cOut (commitBudget tau kappa * (3 * (fuel + 1) + 2)) (commitBudget tau kappa)

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*} (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The seed-collision bound. -/
theorem seedCollision_le (hvc : verifyBudget ≤ commitBudget tau kappa) (hin : Function.Injective V.layout.input)
    (hkey : Function.Injective V.layout.key) (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (cOut : Nat) (hout : ∀ b, Fintype.card {r : Bits lambda // V.layout.output r = b} ≤ cOut) (fuel : Nat) :
    (randomEventExperiment S V verifyBudget publicKey sampleWitness adversary (seedCollision V) fuel) true ≤
      εCollOf lambda tau kappa cOut fuel := by
  have hlambda : 0 < lambda := by omega
  set B := 3 * (fuel + 1) + 2 with hB
  set ε : ℝ≥0∞ := callCost lambda cOut (commitBudget tau kappa * B) (commitBudget tau kappa) with hε
  have hpub' : ∀ (query : Query lambda) (world) (n : Nat) (r), InvC (tau := tau) (kappa := kappa) n world →
      r ∈ ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query
        world).support → InvC (tau := tau) (kappa := kappa) (n + 1) r.2 :=
    fun query world n r h hr => invC_pub S V verifyBudget publicKey sampleWitness query world n r h hr
  have hsignP : ∀ (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool) (world) (n : Nat),
      InvC (tau := tau) (kappa := kappa) n world → n ≤ B →
      mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message w')
          fun r => pairMass V.layout.output (companionL V.layout hin) r.2.other.cipherHistory) ≤
        pairMass V.layout.output (companionL V.layout hin) world.other.cipherHistory + ε :=
    fun sk message world n h hn =>
      (honest_pair_bound S V verifyBudget publicKey sampleWitness V.layout.output (companionL V.layout hin)
        (companionL_involutive V.layout hin) (companionL_ne V.layout hin hlambda) cOut hout sk message world n h).trans
        (add_le_add le_rfl (callCost_mono_len _ _ _ (Nat.mul_le_mul_left _ hn)))
  have hpubP : ∀ (query : Query lambda) (world) (n : Nat), InvC (tau := tau) (kappa := kappa) n world → n ≤ B →
      mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query w')
          fun r => pairMass V.layout.output (companionL V.layout hin) r.2.other.cipherHistory) ≤
        pairMass V.layout.output (companionL V.layout hin) world.other.cipherHistory + ε :=
    fun query world n h hn =>
      (public_pair_bound S V verifyBudget publicKey sampleWitness V.layout.output (companionL V.layout hin)
        (companionL_involutive V.layout hin) (companionL_ne V.layout hin hlambda) cOut hout query world n h).trans
        (add_le_add le_rfl (callCost_mono_len _ _ _ (Nat.mul_le_mul_left _ hn)))
  have hprepP : ∀ (pk message : List Bool) (signature) (world) (n : Nat), InvC (tau := tau) (kappa := kappa) n world →
      n ≤ B →
      mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification pk
          message signature w') fun r => pairMass V.layout.output (companionL V.layout hin) r.2.other.cipherHistory) ≤
        pairMass V.layout.output (companionL V.layout hin) world.other.cipherHistory + ε :=
    fun pk message signature world n h hn =>
      (prepare_pair_bound S V verifyBudget publicKey sampleWitness V.layout.output (companionL V.layout hin)
        (companionL_involutive V.layout hin) (companionL_ne V.layout hin hlambda) cOut hout hvc pk message signature world
        n h).trans (add_le_add le_rfl (callCost_mono_len _ _ _ (Nat.mul_le_mul_left _ hn)))
  unfold randomEventExperiment
  rw [mean_bind_apply]
  refine mean_le_const _ _ _ fun index _ => ?_
  unfold eventExperiment cutExperiment
  rw [keygen_resampled S V verifyBudget publicKey sampleWitness]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [mean_bind_apply]
  refine mean_le_const _ _ _ fun g hg => ?_
  rw [PMF.bind_comm, mean_bind_apply]
  refine mean_le_const _ _ _ fun state _ => ?_
  rw [← PMF.bind_bind, cut_postLaw resample resample_idem _ adversary (honest_postLaw S V verifyBudget publicKey sampleWitness)
    (publicOracle_postLaw S V verifyBudget publicKey sampleWitness), PMF.bind_bind]
  simp only [mean_bind_apply, mean_bind]
  have hinv0 : InvC (tau := tau) (kappa := kappa) 0 g.2.2 := invC_keygen S V verifyBudget publicKey sampleWitness g hg
  have hnil : g.2.2.other.cipherHistory = [] := by
    have hlen := hinv0.2.2
    rw [Nat.mul_zero, Nat.le_zero] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  calc mean (resampleW resample g.2.2) (fun w =>
          mean (cut (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index.val
              (fuel + 1) g.1 g.2.1 state w ⟨[], [], []⟩) fun c =>
            mean (resampleCut resample c) fun c' =>
              (match c' with
                | .ended _ => PMF.pure false
                | .saved snapshot =>
                  (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
                    snapshot).map (seedCollision V snapshot)) true)
      ≤ mean (resampleW resample g.2.2) (fun w =>
          mean (cut (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index.val
              (fuel + 1) g.1 g.2.1 state w ⟨[], [], []⟩) fun c =>
            cutMass V.layout.output (companionL V.layout hin) c + ((2 * (fuel + 1) : Nat) : ℝ≥0∞) * ε) := by
        refine mean_le_mean _ _ _ fun w hw => mean_le_mean _ _ _ fun c hc => ?_
        cases c with
        | ended t =>
          simp only [resampleCut, mean_pure, cutMass, PMF.pure_apply]
          simp
        | saved sn =>
          simp only [resampleCut, mean_map, cutMass]
          have hsn : InvC (tau := tau) (kappa := kappa) (0 + (fuel + 1)) sn.world :=
            cut_saved_gen (InvC (tau := tau) (kappa := kappa)) invC_mono invC_query _ adversary
              (invC_honest S V verifyBudget publicKey sampleWitness) hpub' index.val (fuel + 1) _ _ state _ _ 0
              (invC_resample 0 g.2.2 hinv0 w hw) _ hc sn rfl
          have hrem := cut_remaining_le _ adversary index.val (fuel + 1) _ _ state _ _ _ hc sn rfl
          refine (fork_pair_bound _ adversary V.layout.output (companionL V.layout hin) ε B (InvC (tau := tau) (kappa := kappa))
            invC_mono invC_resample invC_query (invC_honest S V verifyBudget publicKey sampleWitness) hpub'
            (invC_prep S V verifyBudget publicKey sampleWitness hvc) invC_update invC_restore (fun _ _ h => h.2.1)
            (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
            (prepareVerification_postLaw S V verifyBudget publicKey sampleWitness)
            (honest_keepsFamily S V verifyBudget publicKey sampleWitness)
            (publicOracle_keepsFamily S V verifyBudget publicKey sampleWitness)
            (prepareVerification_keepsFamily S V verifyBudget publicKey sampleWitness)
            (honest_grows S V verifyBudget publicKey sampleWitness) (publicOracle_grows S V verifyBudget publicKey sampleWitness)
            (prepareVerification_grows S V verifyBudget publicKey sampleWitness)
            (honest_shiftLaw S V verifyBudget publicKey sampleWitness) (publicOracle_shiftLaw S V verifyBudget publicKey sampleWitness)
            (prepareVerification_shiftLaw S V verifyBudget publicKey sampleWitness) hsignP hpubP hprepP (seedCollision V)
            (seedCollision_none V) (fun s' l r h g hg => seedCollision_witnessed V hin hkey hl hL s' l r h g hg) sn
            (0 + (fuel + 1)) hsn (by omega)).trans ?_
          exact add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr (by omega)) le_rfl)
    _ = mean (resampleW resample g.2.2) (fun w =>
          mean (cut (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary index.val
              (fuel + 1) g.1 g.2.1 state w ⟨[], [], []⟩) (cutMass V.layout.output (companionL V.layout hin))) +
          ((2 * (fuel + 1) : Nat) : ℝ≥0∞) * ε := by
        simp only [mean_add_const]
    _ ≤ pairMass V.layout.output (companionL V.layout hin) g.2.2.other.cipherHistory + ((fuel + 1 : Nat) : ℝ≥0∞) * ε +
          ((2 * (fuel + 1) : Nat) : ℝ≥0∞) * ε :=
        add_le_add (cut_pair_bound _ adversary V.layout.output (companionL V.layout hin) ε B (InvC (tau := tau) (kappa := kappa))
          invC_resample invC_query (invC_honest S V verifyBudget publicKey sampleWitness) hpub'
          (honest_postLaw S V verifyBudget publicKey sampleWitness) (publicOracle_postLaw S V verifyBudget publicKey sampleWitness)
          hsignP hpubP (fuel + 1) index.val _ _ state _ _ 0 hinv0 (by omega)) le_rfl
    _ = εCollOf lambda tau kappa cOut fuel := by
        rw [hnil, pairMass_nil, zero_add, εCollOf, ← add_mul]
        push_cast
        ring

end
end SDitH.Proofs.SeedCollisionBound
