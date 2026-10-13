import SDitH.Proofs.TouchPrep
import SDitH.Proofs.TouchTotal

/-! The swap's touching term as the touching total's probability. For a
fixed salt and digest, the call on the resampled world followed by the
touching functional at the output's hidden keys from the resampled pruned
world, averaged over the uniform root, is the touching probability of the
touching total: the joint draw of the root and the family, the view of the
commitment run pruned at the signature's hidden keys with the family
stripped, and the continuation that resamples the family and runs the
game's process. -/

namespace SDitH.Proofs.TouchIdentity

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.CandidateVerifier Spec.CandidateSimulator Spec.BLC
open Spec.SharedSigner (commitBudget Committed)
open Spec.BAVC (Digest)
open Spec.PIOPArithmetic (selectorCount)
open Spec.IdealCipher (Family Entry)
open Spec.RandomOracleTrap (indicator)
open Spec.SlopeConsistencyGame (Out)
open Spec.HashCipherProgram (Program)
open CandidateResample CipherInvariant HiddenEntries GamePrune SignBridge SwapDischarge SharedPrune HiddenTuple HiddenSlice
open GameResample CipherResample ChargeExpect ChargeCutExpect TouchSplit TouchAssembly TouchTotal RootPosteriorBound
open CommitViewExchange ForkOutcome TouchPrep
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths) (publicKey : List Bool)

/-- The post-processing of the touching total: the simulated post-processing
with the outer hash table. -/
def postT (message : List Bool) (salt : Bits lambda) (digest : Digest lambda)
    (table : HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))
    (p : Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda)
      (Committed F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))) :
    PMF (Signature (Digest lambda)
        (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))) :=
  simPost S publicKey message salt digest p table

/-- The hidden tuple of the touching total's output: the signature's. -/
def hiddenT (q : Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))) :
    Fin tau → Fin (2 ^ kappa) :=
  sigHidden S q.1

variable (Gc : Signature (Digest lambda)
    (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) →
  GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
    (selectorCount widths * w) (lambda * (widths.length - 1)) →
  PMF (GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
    (selectorCount widths * w) (lambda * (widths.length - 1))))

/-- The continuation of the touching total: the family resampled from the
view's history, then the game's process from the signature and the world
with the output's table. -/
def contT (v : (Signature (Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)) ×
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount) → Option (Digest lambda))) ×
    World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) :
    PMF (GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1))) :=
  (posterior v.2.cipherHistory).bind fun f => Gc v.1.1 ⟨v.1.2, { v.2 with family := f }⟩

/-- The recorded entries: the final world's cipher history. -/
def newT (y : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
    (selectorCount widths * w) (lambda * (widths.length - 1))) : List (Entry (Bits lambda) (Bits lambda)) :=
  y.other.cipherHistory

/-- The swap's touching term over the uniform root is the touching total's
probability. -/
theorem touchInner_eq_touchAll (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt : Bits lambda)
    (digest : Digest lambda)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1))) :
    mean (PMF.uniformOfFintype (Bits lambda)) (fun root =>
      touchInner S publicKey (sigHidden S) wsign message salt root digest world (fun K r =>
        mean (Gc r.1 r.2) fun y => indicator (touchesG K y))) =
    mean (rootDraw world.other.cipherHistory)
      (touchAll S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc)
        newT) := by
  rw [mean_rootDraw]
  refine congrArg _ (funext fun root => ?_)
  have hres : ∀ G : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)) → ℝ≥0∞,
      mean (resampleW resample world) G =
        mean (posterior world.other.cipherHistory) fun g => G { world with other := { world.other with family := g } } := by
    intro G
    simp only [resampleW, resample, mean_map]
  unfold touchInner
  rw [hres]
  refine congrArg _ (funext fun g => ?_)
  unfold touchAll viewAct viewPruned commitOracle
  simp only [mean_bind, mean_map]
  refine mean_congr_support _ _ _ fun r₀ hr₀ => ?_
  have hg : r₀.2.family = g := runProgram_family _ _ _ r₀ hr₀
  refine congrArg _ (funext fun q => ?_)
  simp only [outKeys, hg, hiddenT, contT, newT, resampleW, resample, pruneW, mean_map, mean_bind, touchesG, touchesW]
  rfl

variable (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- A world with another consistent family keeps the extended invariant. -/
theorem invC_setFamily (n : Nat)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (h : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) n world) (g : Family (Bits lambda) (Bits lambda))
    (hg : Spec.IdealCipher.Matches g world.other.cipherHistory) :
    InvC (tau := tau) (kappa := kappa) n { world with other := { world.other with family := g } } :=
  ⟨h.1, hg, h.2.2⟩

include V verifyBudget sampleWitness in
/-- The expected recorded length of the touching total's continuation is at
most the commitment budget times the end budget, when the game's process
keeps the invariant to the end budget. -/
theorem expLen_le (wsign : Fin (selectorCount widths * w) → ZMod 2) (message : List Bool) (salt : Bits lambda)
    (digest : Digest lambda) (m B' : Nat)
    (world : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))
    (hw : InvC (lambda := lambda) (s := s) (higherCount := higherCount) (w := w) (widths := widths) (F := F) (tau := tau)
      (kappa := kappa) m world)
    (hGc : ∀ sig w'', InvC (tau := tau) (kappa := kappa) (m + 1) w'' → ∀ y ∈ (Gc sig w'').support,
      InvC (tau := tau) (kappa := kappa) B' y)
    (x : Bits lambda × Family (Bits lambda) (Bits lambda)) (hx : Spec.IdealCipher.Matches x.2 world.other.cipherHistory) :
    expLen S.signer salt wsign world.other (postT S publicKey message salt digest world.hashTable) (hiddenT S) (contT Gc) newT x ≤
      commitBudget tau kappa * B' := by
  unfold expLen viewAct viewPruned
  simp only [mean_bind, mean_map]
  refine mean_le_const _ _ _ fun r₀ hr₀ => mean_le_const _ _ _ fun q hq => ?_
  -- the world after the call, as the oracle's output
  set w' : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)) := { world with other := { world.other with family := x.2 } }
    with hw'
  have hinv' : InvC (tau := tau) (kappa := kappa) m w' := invC_setFamily m world hw x.2 hx
  have hmem : (q.1, (⟨q.2, r₀.2⟩ : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
      (selectorCount widths * w) (lambda * (widths.length - 1)))) ∈
      (commitOracle S.signer salt wsign x.1 (simPost S publicKey message salt digest) w').support := by
    unfold commitOracle
    simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff]
    exact ⟨r₀, hr₀, q, hq, rfl⟩
  have hinv1 := invC_commitOracle S V verifyBudget publicKey sampleWitness salt x.1 wsign message digest m w' hinv' _ hmem
  set K := hiddenKeysAll S.signer.layout r₀.2.family S.signer.variant salt x.1 (hiddenT S q) with hK
  have hinv2 := invC_pruneW K (m + 1) _ hinv1
  unfold contT
  simp only [mean_bind]
  refine mean_le_const _ _ _ fun f hf => mean_le_const _ _ _ fun y hy => ?_
  have hmem' : (⟨q.2, { stripFamily (pruneShared K r₀.2) with family := f }⟩ :
      GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Digest lambda) lambda s
        (selectorCount widths * w) (lambda * (widths.length - 1))) ∈
      (resampleW resample (pruneW K (⟨q.2, r₀.2⟩ : GW (HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
        (Digest lambda) lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))).support := by
    simp only [resampleW, resample, PMF.mem_support_map_iff]
    exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  have hinv3 := invC_resample (m + 1) _ hinv2 _ hmem'
  have hinvy := hGc q.1 _ hinv3 y hy
  unfold newT
  exact_mod_cast hinvy.2.2

end
end SDitH.Proofs.TouchIdentity
