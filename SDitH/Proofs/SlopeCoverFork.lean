import SDitH.Proofs.SlopeChainFork
import SDitH.Proofs.InvCExtra

/-! The fork-level coverage of the stored-mask slope event: on a snapshot
whose world is well formed, without the mention and digest-collision
events on its trace, and with both branches' histories matching the
snapshot's family, the event forces one of: a mask trap on the snapshot's
trace (the stored mask answered after the claim's chain was present and
killing the nonzero slope difference), a witnessed pair in the union of
the two histories, or an unseen seed matching a named seed's two
commitment halves. This is the shared slope game's coverage read on the
snapshot's trace and the union history. -/

namespace SDitH.Proofs.SlopeCoverFork

open Spec.BAVC Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay
open Spec.SharedScheme Spec.SharedSigning Spec.CandidateScheme Spec.HashCipherEvaluation Spec.CandidateVerifier
open Spec.SlopeConsistency Spec.ConsistencyMatrix Spec.CandidateBAVC Spec.BAVCChainInputs
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open Spec.SharedSlopeGame Spec.SeedPrimitives Spec.SeedPairing Spec.IdealCipher Spec.IdealCipherPairCollision
open Spec.RandomOracleMention Spec.ProductOracle Spec.OracleChain
open Spec.RandomOracleTrace (Traced Extends traceBad)
open BranchAccounting (MaskAfterCut)
open CandidateReduction SlopeEventSetting SlopeChainFork SharedSlopeGame SharedGameInvariant CipherInvariant
open CandidateGameBounds
open scoped Classical

noncomputable section

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F]
  (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
  (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))

/-- The mask trap on the snapshot's trace. -/
def slopeTrap {State : Type*} (snapshot : Snap F lambda s higherCount w widths State) : Bool :=
  decide (∃ e e' : Fin tau, traceBad (tableMaskTrap (vectorOf (slopeSetting S V) snapshot.world.other.family e e'))
    snapshot.world.other.trace = true)

/-- A witnessed pair in the union of the two branches' histories under the
snapshot's family. -/
def witnessedFork {State : Type*} (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a b _ _ =>
    decide (Witnessed id companion snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory))

/-- An unseen seed matching a named seed's two commitment halves under the
snapshot's family. -/
def unseenFork {State : Type*} (snapshot : Snap F lambda s higherCount w widths State) :
    Option (Br F lambda tau kappa s higherCount w widths × Br F lambda tau kappa s higherCount w widths) → Bool :=
  onAttempts fun a b bodyA bodyB =>
    decide (∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (seed out0 out1 : Bits lambda),
      seed ≠ fullOf V a bodyA bodyB e i ∧
      Unseen (a.world.other.cipherHistory ++ b.world.other.cipherHistory) seed (input0 V.variant bodyA.1 e i) ∧
      Unseen (a.world.other.cipherHistory ++ b.world.other.cipherHistory) seed (companion (input0 V.variant bodyA.1 e i)) ∧
      (⟨fullOf V a bodyA bodyB e i, input0 V.variant bodyA.1 e i, out0⟩ : Entry (Bits lambda) (Bits lambda)) ∈
        a.world.other.cipherHistory ++ b.world.other.cipherHistory ∧
      (⟨fullOf V a bodyA bodyB e i, companion (input0 V.variant bodyA.1 e i), out1⟩ : Entry (Bits lambda) (Bits lambda)) ∈
        a.world.other.cipherHistory ++ b.world.other.cipherHistory ∧
      snapshot.world.other.family seed (input0 V.variant bodyA.1 e i) = out0 ∧
      snapshot.world.other.family seed (companion (input0 V.variant bodyA.1 e i)) = out1)

omit [Field F] [Algebra (ZMod 2) F] [NeZero tau] [DecidableEq F] in
/-- The coverage at the attempts. -/
theorem covered {State : Type*}
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hl : 26 ≤ lambda) (htau : 0 < tau) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (snapshot : Snap F lambda s higherCount w widths State) (hwf : WellFormed snapshot.world.other)
    (hmention : prefixBad (digestMention (mentions lambda tau)) snapshot.world.other.trace = false)
    (hcoll : prefixBad digestCollision snapshot.world.other.trace = false)
    (a b : Att F lambda tau kappa s higherCount w widths) (bodyA bodyB : Bod F lambda tau kappa s higherCount w widths)
    (hmatches : Matches snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory))
    (h : ∃ c : Claim lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)),
      c.salt = bodyA.1 ∧ c.full = fullOf V a bodyA bodyB ∧ c.aux = bodyA.2.1 ∧
      ChainIn' (slopeSetting S V) snapshot.world.other.family snapshot.world.other.hashTable c ∧
      Queried (slopeSetting S V) snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) c ∧
      ∃ pm, snapshot.world.other.hashTable (maskInput c.auxiliary) = some pm ∧
        ∃ e e', slopeOf (slopeSetting S V) c e ≠ slopeOf (slopeSetting S V) c e' ∧
          ∀ a', masked pm.2 (slopeOf (slopeSetting S V) c e) a' = masked pm.2 (slopeOf (slopeSetting S V) c e') a') :
    (∃ e e' : Fin tau, traceBad (tableMaskTrap (vectorOf (slopeSetting S V) snapshot.world.other.family e e'))
        snapshot.world.other.trace = true) ∨
      Witnessed id companion snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) ∨
      ∃ (e : Fin tau) (i : Fin (2 ^ kappa)) (seed out0 out1 : Bits lambda),
        seed ≠ fullOf V a bodyA bodyB e i ∧
        Unseen (a.world.other.cipherHistory ++ b.world.other.cipherHistory) seed (input0 V.variant bodyA.1 e i) ∧
        Unseen (a.world.other.cipherHistory ++ b.world.other.cipherHistory) seed (companion (input0 V.variant bodyA.1 e i)) ∧
        (⟨fullOf V a bodyA bodyB e i, input0 V.variant bodyA.1 e i, out0⟩ : Entry (Bits lambda) (Bits lambda)) ∈
          a.world.other.cipherHistory ++ b.world.other.cipherHistory ∧
        (⟨fullOf V a bodyA bodyB e i, companion (input0 V.variant bodyA.1 e i), out1⟩ : Entry (Bits lambda) (Bits lambda)) ∈
          a.world.other.cipherHistory ++ b.world.other.cipherHistory ∧
        snapshot.world.other.family seed (input0 V.variant bodyA.1 e i) = out0 ∧
        snapshot.world.other.family seed (companion (input0 V.variant bodyA.1 e i)) = out1 := by
  obtain ⟨c, hsalt, hfull, haux, hchain, hqueried, pm, hpm, e, e', hne, hmask⟩ := h
  obtain ⟨htraced, hord, hfresh, -, -⟩ := hwf
  set fam := snapshot.world.other.family with hfam
  set P := snapshot.world.other.hashTable with hP
  set U := a.world.other.cipherHistory ++ b.world.other.cipherHistory with hU
  have hfree : DigestCollisionFree P :=
    SlopeConsistency.collision_free_of_not_prefix _ _ htraced (by simp [hcoll])
  by_cases hlocal : NoCollisionAt (slopeSetting S V) fam c
  · left
    obtain ⟨em, hem, hemi, hema, -, hemext⟩ := htraced.1 _ pm hpm
    have hN : 0 < 2 ^ kappa := Nat.two_pow_pos kappa
    rcases chain_present_or_mention_of_invariants (by omega) htau hN snapshot.world.other.trace P hord hfresh htraced
      c.salt (rows (commitOf (slopeSetting S V).variant fam c.salt) c) c.rowHashes c.root (tail (slopeSetting S V).encoding c)
      c.auxiliary hchain.1 hchain.2.1 hchain.2.2 em hem hemi with hpresent | hbad
    · have hcin := chainIn_before (slopeSetting S V) fam em.before P hemext c hchain hpresent
      have hfreeB := SlopeConsistency.collision_free_mono em.before P hemext hfree
      have hvec := vectorOf_eq (slopeSetting S V) fam hencoding em.before hfreeB c hlocal hcin e e'
      refine ⟨e, e', List.any_eq_true.mpr ⟨em, hem, ?_⟩⟩
      rw [hemi, hema]
      show tableMaskTrap (vectorOf (slopeSetting S V) fam e e') em.before (maskInput c.auxiliary) pm = true
      rw [tableMaskTrap, Spec.RandomOracleTrap.kernelTrap]
      refine SlopeConsistencyGame.decide_true_of ?_
      rw [hvec]
      refine ⟨sub_ne_zero.mpr hne, fun a' => ?_⟩
      rw [ConsistencyMatrix.masked_sub, hmask a', sub_self]
    · exact absurd hbad (by simp [hmention])
  · rcases collision_split (slopeSetting S V) hl hL fam U hmatches c hqueried hlocal with hw | hu
    · exact Or.inr (Or.inl hw)
    · right; right
      obtain ⟨e, i, seed, hne', hu0, hu1, h0, h1⟩ := hu
      obtain ⟨hq0, hq1⟩ := hqueried e i
      rw [hfull] at hne' h0 h1 hq0 hq1
      rw [hsalt] at hu0 hu1 h0 h1 hq0 hq1
      exact ⟨e, i, seed, _, _, hne', hu0, hu1, hq0, hq1, h0, h1⟩

variable (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
  {State : Type*}
  (adversary : Adversary (List Bool) (List Bool)
    (Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
    (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)

/-- The snapshot's family matches the histories of both branches' attempts. -/
theorem fork_consistent (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support)
    (left right) (hres : result = some (left, right)) :
    (∀ a, left.checked.terminal = .attempt a →
      Matches snapshot.world.other.family a.world.other.cipherHistory) ∧
    ∀ b, right.checked.terminal = .attempt b →
      Matches snapshot.world.other.family b.world.other.cipherHistory := by
  set Q : World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)) → Prop :=
    fun world => world.family = snapshot.world.other.family ∧ Matches world.family world.cipherHistory with hQ
  have hpQ := candidate_preserves S V verifyBudget publicKey sampleWitness Q
    (fun budget program world result hr hQw =>
      ⟨(ForkOutcome.runProgram_family budget program world result hr).trans hQw.1,
        (runProgram_cipher budget program world result hr hQw.2).1⟩)
  have hsnapQ : Q snapshot.world.other := by
    refine ⟨rfl, ?_⟩
    have hpC := candidate_preserves S V verifyBudget publicKey sampleWitness Consistent
      (fun budget program world result hr hQw => (runProgram_cipher budget program world result hr hQw).1)
    obtain ⟨generated, hgen, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
    obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
    have hinit : Consistent generated.2.2.other := (invC_keygen S V verifyBudget publicKey sampleWitness generated hgen).2.1
    exact (SharedGameInvariant.cut_preserves _ Consistent hpC adversary index fuel _ _ state _ _ c hcut hinit).1 snapshot hsnap
  obtain ⟨hA, hB⟩ := SharedGameInvariant.fork_preserves _ _ hpQ adversary snapshot hsnapQ result hr left right hres
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨hf, hm⟩ := hA a ha
    rw [← hf]; exact hm
  · obtain ⟨hf, hm⟩ := hB b hb
    rw [← hf]; exact hm

/-- A winning fork without the charged events is one of the named events,
with the mask trap, the witnessed pair and the unseen match in place of
the slope event, or an extraction. -/
theorem good_implies_events_D (hlayout : V.layout = Spec.BAVCCipherProgram.fullLayout lambda) (hl : 26 ≤ lambda)
    (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (hlambda : 0 < lambda) (htau : 0 < tau) (encode : (Fin tau → Fin (2 ^ kappa)) → F)
    (hmid : V.middle = candidateMiddle S.signer.xi S.signer.p V.nodes encode S.signer.randomCount S.signer.enough)
    (hencoding : Function.Injective (fun corrections : Fin (tau - 1) →
      Fin (s + (selectorCount widths * w + lambda * (widths.length - 1))) → ZMod 2 =>
      Spec.BLCHashChain.sourceTail V.encoding corrections))
    (hlinesEnc : ∀ (plain plain' : Fin s → ZMod 2) (base base' : Fin s → Fin tau → Fin kappa → ZMod 2),
      V.encoding.vector plain ++ V.encoding.base base = V.encoding.vector plain' ++ V.encoding.base base' →
        plain = plain' ∧ base = base')
    (hencode : encode = fun hidden => Spec.BLC.psi S.signer.xi (Spec.BLC.challengeRow Spec.GrayCode.grayFieldRow hidden))
    (index fuel : Nat) (c)
    (hc : c ∈ (cutExperiment (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness)) adversary
      index fuel).support)
    (snapshot) (hsnap : c = .saved snapshot)
    (result) (hr : result ∈ (forkAt (scheme (Spec.CandidateScheme.components S V verifyBudget publicKey sampleWitness))
      adversary snapshot).support)
    (hgood : (forkWins snapshot.input result && !CandidateForkOutcome.forkBad (tau := tau) snapshot result) = true) :
    (maskAfter snapshot result || notSeparated V result || seedCollision V snapshot result ||
      (slopeTrap S V snapshot || witnessedFork snapshot result || unseenFork V snapshot result) ||
      zeroChallenge V encode result || schwartzZippel S V encode snapshot result || extracts S V snapshot result) = true := by
  have hC := good_implies_events_C S V verifyBudget publicKey sampleWitness adversary hlayout hl hL hlambda htau encode hmid
    hencoding hlinesEnc hencode index fuel c hc snapshot hsnap result hr hgood
  have hwf := snapshot_wellFormed S V verifyBudget publicKey sampleWitness adversary index fuel c hc snapshot hsnap
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hgood
  have hforkBad := hgood.2
  simp only [Bool.or_eq_true] at hC ⊢
  rcases hC with ((((((h1 | h2) | h3) | h4) | h5) | h6) | h7)
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h2)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h3))))
  · -- the slope event is covered
    refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
    rcases result with _ | ⟨left, right⟩
    · exact absurd h4 (by simp [slopeWinC, onAttempts])
    obtain ⟨hmA, hmB⟩ := fork_consistent S V verifyBudget publicKey sampleWitness adversary index fuel c hc snapshot hsnap
      _ hr left right rfl
    simp only [CandidateForkOutcome.forkBad, Bool.or_eq_false_iff] at hforkBad
    obtain ⟨⟨hmention, hcoll⟩, -, -⟩ := hforkBad
    simp only [SharedMentionBound.mentionEvent] at hmention
    simp only [SharedCollisionBound.collisionEvent] at hcoll
    simp only [slopeWinC, witnessedFork, unseenFork, onAttempts] at h4 ⊢
    revert h4
    cases ha : left.checked.terminal with
    | attempt a =>
      cases hb : right.checked.terminal with
      | attempt b =>
        intro h4
        simp only at h4 ⊢
        rcases hba : a.signature.body with _ | bodyA
        · rw [hba] at h4; simp at h4
        rcases hbb : b.signature.body with _ | bodyB
        · rw [hba, hbb] at h4; simp at h4
        rw [hba, hbb] at h4
        simp only at h4 ⊢
        have hmatches : Matches snapshot.world.other.family (a.world.other.cipherHistory ++ b.world.other.cipherHistory) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hmA a ha x hx
          · exact hmB b hb x hx
        rcases covered S V hencoding hl htau hL snapshot hwf hmention hcoll a b bodyA bodyB hmatches
          (of_decide_eq_true h4) with ht | hw | hu
        · exact Or.inl (Or.inl (decide_eq_true ht))
        · exact Or.inl (Or.inr (decide_eq_true hw))
        · exact Or.inr (decide_eq_true hu)
      | exhausted t => intro h4; simp at h4
      | aborted t => intro h4; simp at h4
      | rejected t => intro h4; simp at h4
    | exhausted t => intro h4; simp at h4
    | aborted t => intro h4; simp at h4
    | rejected t => intro h4; simp at h4
  · exact Or.inl (Or.inl (Or.inr h5))
  · exact Or.inl (Or.inr h6)
  · exact Or.inr h7

end
end SDitH.Proofs.SlopeCoverFork
