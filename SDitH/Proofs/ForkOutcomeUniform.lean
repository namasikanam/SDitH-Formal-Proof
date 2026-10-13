import SDitH.Proofs.ForkSlopeUniform
import SDitH.Proofs.ForkGoodOutcome

/-! The fork outcomes with the data shared across executions explicit.
The prefix restriction, the deterministic fork outcome and the good-fork
outcome are restated through the uniform fork-to-slope lemma: unless a
branch event or a collision occurred, the two reconstructions, the
auxiliary digest and the stored mask are fixed, and at every execution
with differing hidden indices either a recorded seed collision occurs
there or the masked slope identity holds for the merge completion at the
stored mask. -/

namespace SDitH.Proofs.ForkOutcomeUniform

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace
open Spec.SharedScheme Spec.SharedSigning Spec.HashCipherEvaluation Spec.CandidateVerifier Spec.SlopeConsistency
open Spec.BLCSeedExtraction Spec.BLCSeedLines Spec.BAVC
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open ForkSlopePrefix (hashInputs)
open ForkOutcome (BranchEvent)
open ForkEventUnion (forkBad)
open BranchAccounting (MaskAfterCut)
open scoped Classical
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The uniform slope data on a table: the reconstructions, the auxiliary
digest and the stored mask, with the per-execution alternative. -/
def UniformSlope {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (V : VerifierSetting F lambda tau kappa s wit rnd)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (P : List Bool → Option (Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (saltL saltR : Bits lambda)
    (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (piopL piopR : Digest lambda)
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau) : Prop :=
  ∃ (reconL reconR : Reconstructed lambda tau (2 ^ kappa)) (auxD : Digest lambda) (pm : Out lambda s wit rnd),
    saltL = saltR ∧ auxL.corrections = auxR.corrections ∧ auxL.plain = auxR.plain ∧
    Evaluates family (SharedSchemeChain.projected P) ciphers
      (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant saltL (V.expand piopL decL.1) decL.2 V.Topen V.nodes)
      (Except.ok reconL) ∧
    Evaluates family (SharedSchemeChain.projected P) ciphers
      (Spec.BAVCReconstructionProgram.reconstruct V.layout V.variant saltR (V.expand piopR decR.1) decR.2 V.Topen V.nodes)
      (Except.ok reconR) ∧
    P (Spec.BAVCChainInputs.maskInput auxD) = some pm ∧
    ∀ e : Fin tau, V.expand piopL decL.1 e ≠ V.expand piopR decR.1 e →
      (∃ (i : Fin (2 ^ kappa)) (ls rs : Seed lambda),
          Spec.BAVCBinding.IsSeedCollision
            (Spec.BAVCReconstructionProgram.primitives (tau := tau) (N := 2 ^ kappa) V.layout V.variant family
              (SharedSchemeChain.projected P))
            saltL (Spec.SeedTree.leafOffset e i) ls rs ∧
          ∀ side : Bool,
            Spec.IdealCipher.entry (.encrypt (V.layout.key ls)
              (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
              (family (V.layout.key ls) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers ∧
            Spec.IdealCipher.entry (.encrypt (V.layout.key rs)
              (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side)))
              (family (V.layout.key rs) (V.layout.input (Spec.SeedPrimitives.cipherInput V.variant saltL (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i) side))) ∈ ciphers) ∨
        ∀ a, maskedSlope p saltL (fun e' i => merge reconL reconR e' i) randomCount enough auxL pm.2 e a = auxL.plain a

/-- The prefix restriction with uniform data. -/
theorem fork_masked_slope_prefix_uniform {F : Type*} [Field F] [Algebra (ZMod 2) F] (xi : F)
    (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (randomCount : Nat) (enough : s + (wit + rnd) ≤ 8 * randomCount)
    (V : VerifierSetting F lambda tau kappa s wit rnd)
    (hmid : V.middle = candidateMiddle xi p V.nodes encode randomCount enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) → Fin (s + (wit + rnd)) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (saltL saltR : Bits lambda) (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (piopL piopR : Digest lambda)
    (decL decR : Spec.BLCRetry.Counter × Opening lambda tau)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (P tableL tableR : List Bool → Option (Out lambda s wit rnd))
    (hextL : ∀ x y, P x = some y → tableL x = some y) (hextR : ∀ x y, P x = some y → tableR x = some y)
    (ciphersL ciphersR : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (left right : Spec.SignatureComposition.Recomputed F lambda wit rnd)
    (hl : Evaluates family tableL ciphersL (verifyProgram V saltL auxL piopL decL) (Except.ok left))
    (hr : Evaluates family tableR ciphersR (verifyProgram V saltR auxR piopR decR) (Except.ok right))
    (hinL : ∀ x ∈ hashInputs family tableL (verifyProgram V saltL auxL piopL decL), (P x).isSome)
    (hinR : ∀ x ∈ hashInputs family tableR (verifyProgram V saltR auxR piopR decR), (P x).isSome)
    (hlines : left.lines = right.lines) (hfree : DigestCollisionFree P) :
    UniformSlope p randomCount enough V family P (ciphersL ++ ciphersR) saltL saltR auxL auxR piopL piopR decL decR := by
  have hPL : ∀ x ∈ hashInputs family tableL (verifyProgram V saltL auxL piopL decL), P x = tableL x := by
    intro x hx
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hinL x hx)
    rw [hy, hextL x y hy]
  have hPR : ∀ x ∈ hashInputs family tableR (verifyProgram V saltR auxR piopR decR), P x = tableR x := by
    intro x hx
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hinR x hx)
    rw [hy, hextR x y hy]
  have hl' := ForkSlopePrefix.evaluates_mono_ciphers family P ciphersL (ciphersL ++ ciphersR)
    (fun e he => List.mem_append_left _ he) _ _ (ForkSlopePrefix.evaluates_restrict family tableL P ciphersL _ _ hl hPL)
  have hr' := ForkSlopePrefix.evaluates_mono_ciphers family P ciphersR (ciphersL ++ ciphersR)
    (fun e he => List.mem_append_right _ he) _ _ (ForkSlopePrefix.evaluates_restrict family tableR P ciphersR _ _ hr hPR)
  exact ForkSlopeUniform.fork_masked_slope_uniform xi p encode randomCount enough V hmid hencoding hlinesEnc saltL saltR
    auxL auxR piopL piopR decL decR family P (ciphersL ++ ciphersR) left right hl' hr' hlines hfree

section Shared

variable {higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
  (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The deterministic fork outcome with uniform data: a branch event, a
collision of the snapshot's table, or the uniform slope data. -/
theorem fork_outcome_uniform (hlambda : 0 < lambda) (htau : 0 < tau)
    (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (randomCount : Nat)
    (enough : s + (selectorCount widths * w + lambda * (widths.length - 1)) ≤ 8 * randomCount)
    (hmid : V.middle = candidateMiddle xi p V.nodes encode randomCount enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).support)
    (hw : forkWins snapshot.input result = true) :
    ∃ left right a b bodyA bodyB recA recB, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧ a.target ≠ b.target ∧
      Evaluates snapshot.world.other.family a.world.other.hashTable a.world.other.cipherHistory
        (verifyProgram V bodyA.1 bodyA.2.1 a.signature.piop bodyA.2.2.1) (Except.ok recA) ∧
      Evaluates snapshot.world.other.family b.world.other.hashTable b.world.other.cipherHistory
        (verifyProgram V bodyB.1 bodyB.2.1 b.signature.piop bodyB.2.2.1) (Except.ok recB) ∧
      recA.lines = snapshot.input.payload.1 ∧ recB.lines = snapshot.input.payload.1 ∧
      (UniformSlope p randomCount enough V snapshot.world.other.family snapshot.world.other.hashTable
          (a.world.other.cipherHistory ++ b.world.other.cipherHistory) bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1
          a.signature.piop b.signature.piop bodyA.2.2.1 bodyB.2.2.1 ∨
        BranchEvent (tau := tau) snapshot.world.other.hashTable snapshot.input.payload.1 a.world.other ∨
        BranchEvent (tau := tau) snapshot.world.other.hashTable snapshot.input.payload.1 b.world.other ∨
        ¬ DigestCollisionFree snapshot.world.other.hashTable) := by
  obtain ⟨left, right, a, b, hres, ha, hb, _, _, hai, hbi, _, _, hne⟩ :=
    SignatureReplayConsistency.successful_fork_attempts _ adversary snapshot result hr hw
  obtain ⟨_, hleftW, hrightW⟩ := SharedGameInvariant.fork_cutAt S V verifyBudget publicKey sampleWitness adversary
    index fuel c hc snapshot hsnap result hr left right hres
  obtain ⟨haW, haC⟩ := hleftW a ha
  obtain ⟨hbW, hbC⟩ := hrightW b hb
  have hpF := SharedGameInvariant.shared_preserves S V verifyBudget publicKey sampleWitness
    (fun world => world.family = snapshot.world.other.family)
    (fun budget program world result hr hQ => (ForkOutcome.runProgram_family budget program world result hr).trans hQ)
  obtain ⟨hfamA, hfamB⟩ := SharedGameInvariant.fork_preserves _ _ hpF adversary snapshot rfl result hr left right hres
  have hbranch : ∀ branch, branch ∈ (freshBranch (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).support →
      ∀ att, branch.checked.terminal = .attempt att → att.world.other.family = snapshot.world.other.family →
      ∃ body recovered, att.signature.body = some body ∧
        Evaluates snapshot.world.other.family att.world.other.hashTable att.world.other.cipherHistory
          (verifyProgram V body.1 body.2.1 att.signature.piop body.2.2.1) (Except.ok recovered) ∧
        att.input.payload.1 = recovered.lines := by
    intro branch hbr att hatt hfam
    obtain ⟨wv, hwv⟩ := ForkOutcome.branch_attempt_source _ adversary snapshot branch hbr att hatt
    obtain ⟨body, recovered, hbody, heval, hlines, hfam'⟩ :=
      ForkOutcome.attempt_verification S V verifyBudget publicKey sampleWitness _ _ _ wv att.world att.input hwv
    refine ⟨body, recovered, hbody, ?_, hlines⟩
    rw [← hfam, hfam']
    exact heval
  cases he : snapshot.world.hashTable snapshot.input with
  | some _ =>
    simp only [forkAt, he, PMF.mem_support_pure_iff] at hr
    subst hr
    cases hres
  | none =>
    rw [forkAt, he] at hr
    obtain ⟨l, hl, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨rr, hrr, hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
    rw [← hpair] at hres
    cases hres
    obtain ⟨bodyA, recA, hbodyA, hevalA, hlinesA⟩ := hbranch _ hl a ha (hfamA a ha)
    obtain ⟨bodyB, recB, hbodyB, hevalB, hlinesB⟩ := hbranch _ hrr b hb (hfamB b hb)
    refine ⟨_, _, a, b, bodyA, bodyB, recA, recB, hpair.symm, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB,
      by rw [← hlinesA, hai], by rw [← hlinesB, hbi], ?_⟩
    by_cases hfree : DigestCollisionFree snapshot.world.other.hashTable
    swap
    · exact Or.inr (Or.inr (Or.inr hfree))
    have hA := BranchAccounting.branch_visited_or_event hlambda htau xi p encode randomCount enough V hmid bodyA.1 bodyA.2.1
      a.signature.piop bodyA.2.2.1 snapshot.world.other.family a.world.other.hashTable snapshot.world.other.hashTable
      a.world.other.cipherHistory a.world.other.trace haW.2.1 haW.2.2.1 haW.1 haC.1 haC.2 recA hevalA
      snapshot.input.payload.1 (by rw [← hlinesA, hai])
    have hB := BranchAccounting.branch_visited_or_event hlambda htau xi p encode randomCount enough V hmid bodyB.1 bodyB.2.1
      b.signature.piop bodyB.2.2.1 snapshot.world.other.family b.world.other.hashTable snapshot.world.other.hashTable
      b.world.other.cipherHistory b.world.other.trace hbW.2.1 hbW.2.2.1 hbW.1 hbC.1 hbC.2 recB hevalB
      snapshot.input.payload.1 (by rw [← hlinesB, hbi])
    rcases hA with hinA | hevA
    swap
    · exact Or.inr (Or.inl hevA)
    rcases hB with hinB | hevB
    swap
    · exact Or.inr (Or.inr (Or.inl hevB))
    left
    exact fork_masked_slope_prefix_uniform xi p encode randomCount enough V hmid hencoding hlinesEnc
      bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1 a.signature.piop b.signature.piop bodyA.2.2.1 bodyB.2.2.1
      snapshot.world.other.family snapshot.world.other.hashTable a.world.other.hashTable b.world.other.hashTable
      haC.2 hbC.2 a.world.other.cipherHistory b.world.other.cipherHistory recA recB hevalA hevalB hinA hinB
      (by rw [← hlinesA, ← hlinesB, hai, hbi]) hfree

/-- A successful fork without the charged events: the uniform slope data,
or a branch's mask input first queried after the fork. -/
theorem fork_good_outcome_uniform (hlambda : 0 < lambda) (htau : 0 < tau)
    (xi : F) (p : Spec.BLCCommit.Primitives lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (encode : (Fin tau → Fin (2 ^ kappa)) → F) (randomCount : Nat)
    (enough : s + (selectorCount widths * w + lambda * (widths.length - 1)) ≤ 8 * randomCount)
    (hmid : V.middle = candidateMiddle xi p V.nodes encode randomCount enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (components S V verifyBudget publicKey sampleWitness)) adversary index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).support)
    (hw : forkWins snapshot.input result = true) (hgood : forkBad (tau := tau) snapshot result = false) :
    ∃ left right a b bodyA bodyB recA recB, result = some (left, right) ∧
      left.checked.terminal = .attempt a ∧ right.checked.terminal = .attempt b ∧
      a.signature.body = some bodyA ∧ b.signature.body = some bodyB ∧ a.target ≠ b.target ∧
      Evaluates snapshot.world.other.family a.world.other.hashTable a.world.other.cipherHistory
        (verifyProgram V bodyA.1 bodyA.2.1 a.signature.piop bodyA.2.2.1) (Except.ok recA) ∧
      Evaluates snapshot.world.other.family b.world.other.hashTable b.world.other.cipherHistory
        (verifyProgram V bodyB.1 bodyB.2.1 b.signature.piop bodyB.2.2.1) (Except.ok recB) ∧
      recA.lines = snapshot.input.payload.1 ∧ recB.lines = snapshot.input.payload.1 ∧
      (UniformSlope p randomCount enough V snapshot.world.other.family snapshot.world.other.hashTable
          (a.world.other.cipherHistory ++ b.world.other.cipherHistory) bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1
          a.signature.piop b.signature.piop bodyA.2.2.1 bodyB.2.2.1 ∨
        MaskAfterCut snapshot.world.other.hashTable a.world.other.hashTable ∨
        MaskAfterCut snapshot.world.other.hashTable b.world.other.hashTable) := by
  obtain ⟨left, right, a, b, bodyA, bodyB, recA, recB, hres, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB, hlinesA,
    hlinesB, houtcome⟩ := fork_outcome_uniform S V verifyBudget publicKey sampleWitness adversary hlambda htau xi p encode
    randomCount enough hmid hencoding hlinesEnc index fuel c hc snapshot hsnap result hr hw
  have hwell := ForkEventUnion.snapshot_wellFormed S V verifyBudget publicKey sampleWitness adversary index fuel c hc
    snapshot hsnap
  rw [hres] at hgood
  simp only [forkBad, ha, hb, GameEventBound.terminalBad, Bool.or_eq_false_iff] at hgood
  obtain ⟨⟨_, hcollision⟩, hbadA, hbadB⟩ := hgood
  simp only [ForkEventUnion.branchBad, Bool.or_eq_false_iff] at hbadA hbadB
  have hfree : DigestCollisionFree snapshot.world.other.hashTable :=
    SharedCollisionBound.collisionFree_of_not_event _ hwell hcollision
  refine ⟨left, right, a, b, bodyA, bodyB, recA, recB, hres, ha, hb, hbodyA, hbodyB, hne, hevalA, hevalB, hlinesA,
    hlinesB, ?_⟩
  rcases houtcome with huni | hevA | hevB | hcol
  · exact Or.inl huni
  · rcases hevA with ht | hm | hmask
    · exact absurd ht (by simp [SharedTargetBound.targetEvent] at hbadA; simp [hbadA.1])
    · exact absurd hm (by simp [SharedMentionBound.mentionEvent] at hbadA; simp [hbadA.2])
    · exact Or.inr (Or.inl hmask)
  · rcases hevB with ht | hm | hmask
    · exact absurd ht (by simp [SharedTargetBound.targetEvent] at hbadB; simp [hbadB.1])
    · exact absurd hm (by simp [SharedMentionBound.mentionEvent] at hbadB; simp [hbadB.2])
    · exact Or.inr (Or.inr hmask)
  · exact absurd hfree hcol

end Shared

end
end SDitH.Proofs.ForkOutcomeUniform
