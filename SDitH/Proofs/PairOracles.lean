import SDitH.Proofs.PairMass
import SDitH.Proofs.InvCExtra

/-! The pair mass through the candidate scheme's oracles: from a resampled
world with a consistent history of bounded length, the honest signing
oracle, the public oracle and the verification preparation raise the
posterior pair mass of the cipher history by at most one call's cost. -/

namespace SDitH.Proofs.PairOracles

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.HashCipherProgram
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateSimulator Spec.SharedSigner
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher (Matches)
open CipherResample GameResample ChargeExpect SharedResample CandidateResample CandidatePrepLaw
open GamePrune PruneLawRun CandidatePrune CipherInvariant PairMass IdealCipherPairAdaptive TraceGrowth
open scoped Classical ENNReal

noncomputable section

/-- One call's pair cost at history bound `L` and budget `b`. -/
def callCost (lambda capacity L b : Nat) : ℝ≥0∞ :=
  ((b * L + b.choose 2 : Nat) : ℝ≥0∞) * pairCost (Bits lambda) capacity (L + b)

theorem callCost_mono_budget (lambda capacity L : Nat) {b b' : Nat} (h : b ≤ b') :
    callCost lambda capacity L b ≤ callCost lambda capacity L b' := by
  unfold callCost
  refine mul_le_mul' (Nat.cast_le.mpr ?_) (pairCost_mono _ (by omega))
  exact Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.choose_le_choose 2 h)

section Shared

variable {lambda s wit rnd : Nat} {HashInput Digest : Type*} [Fintype Digest] [Nonempty Digest]
  (project companion : Bits lambda → Bits lambda)

omit [Fintype Digest] [Nonempty Digest] in
/-- Resampling keeps the pair mass. -/
theorem mean_resampleW_pairMass (world : GW HashInput Digest lambda s wit rnd) (K : ℝ≥0∞) :
    mean (resampleW resample world) (fun w => pairMass project companion w.other.cipherHistory + K) =
      pairMass project companion world.other.cipherHistory + K := by
  unfold resampleW resample
  rw [mean_map, mean_map]
  show mean _ (fun _ => pairMass project companion world.other.cipherHistory + K) = _
  exact mean_const _ _

omit [Fintype Digest] [Nonempty Digest] in
theorem mean_resampleW_pairMass' (world : GW HashInput Digest lambda s wit rnd) :
    mean (resampleW resample world) (fun w => pairMass project companion w.other.cipherHistory) =
      pairMass project companion world.other.cipherHistory := by
  unfold resampleW resample
  rw [mean_map, mean_map]
  show mean _ (fun _ => pairMass project companion world.other.cipherHistory) = _
  exact mean_const _ _

variable (hinv : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
  (capacity : Nat) (hcap : ∀ target, Fintype.card {output : Bits lambda // project output = target} ≤ capacity)

omit [Fintype Digest] [Nonempty Digest] in
include hinv hnofix hcap in
/-- A program-shaped oracle in mean form. -/
theorem run_mean_bound {A S' : Type*} (budget : Nat)
    (program : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (post : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda) (Bits lambda) A →
      (HashInput → Option Digest) → PMF (S' × (HashInput → Option Digest)))
    (world : GW HashInput Digest lambda s wit rnd) (hcons : Matches world.other.family world.other.cipherHistory)
    (L : Nat) (hL : world.other.cipherHistory.length ≤ L) :
    mean (resampleW resample world) (fun w => mean (Spec.SharedScheme.runProgram budget program w.other) fun r =>
        mean (post r.1 w.hashTable) fun _ => pairMass project companion r.2.cipherHistory) ≤
      pairMass project companion world.other.cipherHistory + callCost lambda capacity L budget := by
  unfold resampleW
  rw [mean_map]
  simp only [mean_const]
  refine (runProgram_pair_bound budget program world.other ⟨_, hcons⟩ (L + budget) (by omega) project companion hinv hnofix
    capacity hcap).trans ?_
  refine add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr ?_) le_rfl)
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hL) le_rfl

omit [Fintype Digest] [Nonempty Digest] in
include hinv hnofix hcap in
/-- A program-shaped oracle raises the pair mass by one call's cost. -/
theorem runOracle_pair_bound {A S' : Type*} (budget : Nat)
    (program : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (post : Program (List Bool) (Spec.SlopeConsistencyGame.Out lambda s wit rnd) (Bits lambda) (Bits lambda) A →
      (HashInput → Option Digest) → PMF (S' × (HashInput → Option Digest)))
    (world : GW HashInput Digest lambda s wit rnd) (hcons : Matches world.other.family world.other.cipherHistory)
    (L : Nat) (hL : world.other.cipherHistory.length ≤ L) :
    mean (resampleW resample world) (fun w => mean (runOracle budget program post w) fun r =>
        pairMass project companion r.2.other.cipherHistory) ≤
      pairMass project companion world.other.cipherHistory + callCost lambda capacity L budget := by
  simp only [runOracle, mean_bind, mean_map]
  exact run_mean_bound project companion hinv hnofix capacity hcap budget program post world hcons L hL

end Shared

section Candidate

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  (project companion : Bits lambda → Bits lambda)
  (hinv : Function.Involutive companion) (hnofix : ∀ input, companion input ≠ input)
  (capacity : Nat) (hcap : ∀ target, Fintype.card {output : Bits lambda // project output = target} ≤ capacity)

/-- The pair mass of a game world. -/
def pm (world : Spec.SignatureSecurity.World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
    (Spec.BAVC.Digest lambda) (World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)))) : ℝ≥0∞ :=
  pairMass project companion world.other.cipherHistory

include hinv hnofix hcap in
/-- The honest signing oracle. -/
theorem honest_pair_bound (sk : List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (message : List Bool)
    (world) (n : Nat)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) :
    mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).sign sk message w') fun r =>
          pm (F := F) (higherCount := higherCount) project companion r.2) ≤
      pm (F := F) (higherCount := higherCount) project companion world +
        callCost lambda capacity (commitBudget tau kappa * n) (commitBudget tau kappa) := by
  rw [honest_sign_shape]
  simp only [mean_bind, mean_map, pm]
  rw [mean_comm]
  refine mean_le_const _ _ _ fun salt _ => ?_
  rw [mean_comm]
  refine mean_le_const _ _ _ fun root _ => ?_
  exact run_mean_bound project companion hinv hnofix capacity hcap (commitBudget tau kappa)
    (commitProgram S.signer salt root sk.2) (honestPost S sk.1 message salt) world h.2.1 _ h.2.2

include hinv hnofix hcap in
/-- The public oracle. -/
theorem public_pair_bound (query : Query lambda) (world) (n : Nat)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) :
    mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).publicOracle query w')
          fun r => pm (F := F) (higherCount := higherCount) project companion r.2) ≤
      pm (F := F) (higherCount := higherCount) project companion world +
        callCost lambda capacity (commitBudget tau kappa * n) (commitBudget tau kappa) := by
  have hone := one_le_commitBudget (tau := tau) (kappa := kappa)
  cases query with
  | hash input =>
    rw [publicOracle_hash_eq]
    exact (runOracle_pair_bound project companion hinv hnofix capacity hcap 1 _ _ world h.2.1 _ h.2.2).trans
      (add_le_add le_rfl (callCost_mono_budget _ _ _ hone))
  | mask input =>
    rw [publicOracle_mask_eq]
    exact (runOracle_pair_bound project companion hinv hnofix capacity hcap 1 _ _ world h.2.1 _ h.2.2).trans
      (add_le_add le_rfl (callCost_mono_budget _ _ _ hone))
  | cipher request =>
    rw [publicOracle_cipher_eq]
    exact (runOracle_pair_bound project companion hinv hnofix capacity hcap 1 _ _ world h.2.1 _ h.2.2).trans
      (add_le_add le_rfl (callCost_mono_budget _ _ _ hone))

include hinv hnofix hcap in
/-- The verification preparation. -/
theorem prepare_pair_bound (hvc : verifyBudget ≤ commitBudget tau kappa) (pk message : List Bool)
    (signature : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (world) (n : Nat)
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) :
    mean (resampleW resample world) (fun w' =>
        mean ((scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)).prepareVerification pk
          message signature w') fun r => pm (F := F) (higherCount := higherCount) project companion r.2) ≤
      pm (F := F) (higherCount := higherCount) project companion world +
        callCost lambda capacity (commitBudget tau kappa * n) (commitBudget tau kappa) := by
  rcases signature with ⟨piop, _ | body⟩
  · rw [prepareVerification_none_eq]
    simp only [mean_pure, pm]
    rw [mean_resampleW_pairMass']
    exact le_self_add
  · rw [prepareVerification_some_eq]
    exact (runOracle_pair_bound project companion hinv hnofix capacity hcap verifyBudget _ _ world h.2.1 _ h.2.2).trans
      (add_le_add le_rfl (callCost_mono_budget _ _ _ hvc))

end Candidate

end
end SDitH.Proofs.PairOracles
