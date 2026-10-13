import SDitH.Proofs.BranchAccounting
import SDitH.Proofs.SharedGameInvariant

/-! The deterministic outcome of a successful fork of the shared game with
the candidate-middle verifier. Every attempt of the run comes from a
verification service call; in the shared model that call is an executed
verification evaluating on the attempt's world, whose lines value is the
attempt's payload digest. At a successful fork both attempts share the
snapshot's typed input, so both verifications carry the snapshot's lines
value, and both branch worlds are well formed and cut at the snapshot's
shared table. Hence, at every execution where the two hidden indices
differ, the fork-to-slope outcome holds on the snapshot's table, or one of
the named branch events occurred, or the snapshot's table has a digest
collision. -/

namespace SDitH.Proofs.ForkOutcome

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace
open Spec.OracleChain Spec.RandomOracleMention Spec.ProductOracle Spec.BAVCChainInputs
open Spec.SharedScheme Spec.SharedSigning Spec.HashCipherProgram Spec.HashCipherEvaluation Spec.CandidateVerifier
open Spec.SlopeConsistency Spec.BLCSeedLines
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open ForkSlopePrefix (hashInputs)
open ForkCutRun (targetBad)
open BranchAccounting (MaskAfterCut)
open SharedGameInvariant (WellFormed CutAt Preserves)
open scoped Classical
noncomputable section

section Generic

variable {Input Digest Key Block A : Type*} [Fintype Digest] [Nonempty Digest]

/-- A run ending in a value evaluates to it, with no budget premise. -/
theorem run_done_evaluates (family : Spec.IdealCipher.Family Key Block) (program : Program Input Digest Key Block A)
    (budget : Nat) (table : Input → Option Digest) (hashes : List (Input × Digest))
    (ciphers : List (Spec.IdealCipher.Entry Key Block))
    (out : Spec.HashCipher.Result Input Digest Key Block (Program Input Digest Key Block A))
    (hout : out ∈ (Spec.HashCipher.runFixed procedure family budget program table hashes ciphers).support)
    (value : A) (hdone : out.state = .done value) : Evaluates family out.hashTable out.cipherHistory program value := by
  induction budget generalizing program table hashes ciphers out with
  | zero =>
    simp only [Spec.HashCipher.runFixed, PMF.mem_support_pure_iff] at hout
    subst out
    cases program with
    | done v => cases hdone; exact .done _
    | hash _ _ => cases hdone
    | cipher _ _ => cases hdone
  | succ budget ih =>
    cases program with
    | done v =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind, PMF.mem_support_pure_iff] at hout
      subst out
      cases hdone
      exact .done _
    | hash input next =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind] at hout
      obtain ⟨result, hq, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨tail, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst out
      have heval := ih (next result.1) result.2 _ ciphers tail ht hdone
      refine .hash input next result.1 value ?_ heval
      exact (HashCipherEvaluation.run_preserves procedure family budget (next result.1) result.2 _ ciphers tail ht).1
        input result.1 (OracleProgram.query_stores_answer table input result hq)
    | cipher request next =>
      simp only [Spec.HashCipher.runFixed, procedure, PMF.pure_bind] at hout
      have heval := ih (next (Spec.IdealCipher.answer family request)) table hashes _ out hout hdone
      refine .cipher request next value ?_ heval
      exact (HashCipherEvaluation.run_preserves procedure family budget (next (Spec.IdealCipher.answer family request))
        table hashes _ out hout).2 (by simp)

end Generic

section Game

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- Every attempt of the run is the output of a verification service call. -/
theorem run_attempt_source (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Query Answer State) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : PublicKey × SecretKey) (state : State)
      (world : World (HashInput PublicKey Message Payload) Digest Other)
      (trace : Trace Message (HashInput PublicKey Message Payload) Query)
      (terminal : Terminal Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query),
      terminal ∈ (Spec.SignatureSecurity.run (scheme components) adversary fuel pk sk state world trace).support →
      ∀ a, terminal = .attempt a →
        ∃ w : World (HashInput PublicKey Message Payload) Digest Other,
          (some a.input, a.world) ∈ ((scheme components).prepareVerification pk a.message a.signature w).support := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace terminal ht a ha
    simp only [Spec.SignatureSecurity.run, PMF.mem_support_pure_iff] at ht
    subst ht
    cases ha
  | succ fuel ih =>
    intro pk sk state world trace terminal ht a ha
    simp only [Spec.SignatureSecurity.run] at ht
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
    cases action with
    | abort =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst hrest
      cases ha
    | finish message signature =>
      obtain ⟨result, hresult, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst hres
      cases hopt : result.1 with
      | none =>
        rw [hopt] at ha
        cases ha
      | some input =>
        rw [hopt] at ha
        cases ha
        refine ⟨world, ?_⟩
        have hr : result = (some input, result.2) := Prod.ext hopt rfl
        rw [← hr]
        exact hresult
    | sign message next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih pk sk _ _ _ terminal hrun a ha
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih pk sk _ _ _ terminal hrun a ha
    | query input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih pk sk _ _ _ terminal hrun a ha

/-- A branch's attempt is the output of a verification service call. -/
theorem branch_attempt_source (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (adversary : Adversary PublicKey Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Query Answer State)
    (snapshot : Snapshot PublicKey (PublicKey × SecretKey) Message (HashInput PublicKey Message Payload) Digest Other Query State)
    (branch : Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (hb : branch ∈ (freshBranch (scheme components) adversary snapshot).support)
    (a : Attempt Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (ha : branch.checked.terminal = .attempt a) :
    ∃ w : World (HashInput PublicKey Message Payload) Digest Other,
      (some a.input, a.world) ∈ ((scheme components).prepareVerification snapshot.publicKey a.message a.signature w).support := by
  obtain ⟨answer, _, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
  obtain ⟨checked, hchecked, hbr⟩ := (PMF.mem_support_map_iff _ _ _).mp hcont
  subst hbr
  obtain ⟨terminal, hterm, hfin⟩ := (PMF.mem_support_bind_iff _ _ _).mp hchecked
  exact run_attempt_source components adversary snapshot.remaining snapshot.publicKey snapshot.secretKey
    (snapshot.next answer) _ _ terminal hterm a ((SharedGameInvariant.finalize_terminal terminal checked hfin).symm.trans ha)

end Game

section Shared

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F]

theorem runProgram_family {A : Type*} {wit rnd : Nat} (budget : Nat)
    (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (result : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd)
    (hr : result ∈ (runProgram budget program world).support) : result.2.family = world.family := by
  obtain ⟨out, _, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  subst hres
  rfl

/-- A shared verification service call producing an input is an executed
verification evaluating on the output world, with the input's lines value
the recovered lines. -/
theorem attempt_verification [NeZero tau] [DecidableEq F]
    (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
    (pk message : List Bool)
    (signature : Signature (Spec.BAVC.Digest lambda)
      (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
    (world world' : World (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))))
    (input : HashInput (List Bool) (List Bool) (Payload F lambda higherCount))
    (h : (some input, world') ∈ ((scheme (components S V verifyBudget publicKey sampleWitness)).prepareVerification
      pk message signature world).support) :
    ∃ (body : Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)
      (recovered : Spec.SignatureComposition.Recomputed F lambda (selectorCount widths * w) (lambda * (widths.length - 1))),
      signature.body = some body ∧
      Evaluates world.other.family world'.other.hashTable world'.other.cipherHistory
        (verifyProgram V body.1 body.2.1 signature.piop body.2.2.1) (Except.ok recovered) ∧
      input.payload.1 = recovered.lines ∧ world'.other.family = world.other.family := by
  obtain ⟨r, hr, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  have hr1 : r.1.map (fun payload => (⟨pk, message, payload⟩ : HashInput (List Bool) (List Bool) (Payload F lambda higherCount))) =
      some input := congrArg Prod.fst hres
  have hr2 : world'.other = r.2 := by
    have := congrArg Prod.snd hres
    simp only at this
    rw [← this]
  change r ∈ (Spec.SharedSigning.prepareVerification S V verifyBudget pk message signature world.other).support at hr
  unfold Spec.SharedSigning.prepareVerification at hr
  rcases hbody : signature.body with _ | body
  · rw [hbody] at hr
    simp only [PMF.mem_support_pure_iff] at hr
    subst hr
    simp at hr1
  · rw [hbody] at hr
    unfold Spec.SharedScheme.prepareVerification at hr
    obtain ⟨run, hrun, hrr⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    subst hrr
    simp only at hr1 hr2
    obtain ⟨out, hout, hout'⟩ := (PMF.mem_support_map_iff _ _ _).mp hrun
    have hforget : Spec.HashCipherTrace.forget out ∈
        (Spec.HashCipher.runFixed procedure world.other.family verifyBudget
          (verifyProgram V body.1 body.2.1 signature.piop body.2.2.1) world.other.hashTable world.other.hashHistory
          world.other.cipherHistory).support := by
      rw [← HashCipherTrace.runFixed_forget]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨out, hout, rfl⟩
    subst hout'
    simp only at hr1 hr2
    cases hstate : out.state with
    | done v =>
      cases v with
      | ok recovered =>
        rw [hstate] at hr1
        simp only [Option.map_some, Option.some.injEq] at hr1
        refine ⟨body, recovered, rfl, ?_, ?_, ?_⟩
        · rw [hr2]
          exact run_done_evaluates world.other.family _ verifyBudget _ _ _ _ hforget (Except.ok recovered) hstate
        · rw [← hr1]
          rfl
        · rw [hr2]
      | error _ =>
        rw [hstate] at hr1
        simp at hr1
    | hash _ _ =>
      rw [hstate] at hr1
      simp at hr1
    | cipher _ _ =>
      rw [hstate] at hr1
      simp at hr1

/-- A named event on one branch world. -/
def BranchEvent {wit rnd : Nat} (P : List Bool → Option (Out lambda s wit rnd)) (target : Spec.BAVC.Digest lambda)
    (world : Spec.SharedScheme.World lambda s wit rnd) : Prop :=
  traceBad (targetBad P target) world.trace = true ∨
    prefixBad (digestMention (mentions lambda tau)) world.trace = true ∨
    MaskAfterCut P world.hashTable

/-- The fork-to-slope outcome on a table with a cipher history. -/
def SlopeOutcome {wit rnd : Nat} (p : Spec.BLCCommit.Primitives lambda tau kappa s wit rnd) (randomCount : Nat)
    (enough : s + (wit + rnd) ≤ 8 * randomCount) (V : VerifierSetting F lambda tau kappa s wit rnd)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (P : List Bool → Option (Out lambda s wit rnd))
    (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda))) (saltL saltR : Bits lambda)
    (auxL auxR : Spec.BLCCommit.Auxiliary tau s wit rnd) (e : Fin tau) : Prop :=
  (∃ (i : Fin (2 ^ kappa)) (ls rs : Spec.BAVC.Seed lambda), saltL = saltR ∧
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
    ∃ (full : Fin tau → Fin (2 ^ kappa) → Bits lambda) (M : Spec.SlopeConsistencyGame.Mask s wit rnd),
      saltL = saltR ∧ auxL.corrections = auxR.corrections ∧ auxL.plain = auxR.plain ∧
      ∀ a, maskedSlope p saltL full randomCount enough auxL M e a = auxL.plain a

/-- The deterministic outcome of a successful fork of the shared game. -/
theorem fork_outcome [NeZero tau] [DecidableEq F] (hlambda : 0 < lambda) (htau : 0 < tau)
    (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
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
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
    {State : Type*}
    (adversary : Adversary (List Bool) (List Bool)
      (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda) (Query lambda)
      (Answer lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) State)
    (index fuel : Nat)
    (c : Spec.SignatureReplay.Cut (List Bool) (List Bool × (Fin (selectorCount widths * w) → ZMod 2)) (List Bool)
      (Signature (Spec.BAVC.Digest lambda) (Option (Body F lambda tau s (selectorCount widths * w) (lambda * (widths.length - 1)) higherCount)))
      (HashInput (List Bool) (List Bool) (Payload F lambda higherCount)) (Spec.BAVC.Digest lambda)
      (Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Query lambda) State)
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
      ∀ e : Fin tau, V.expand a.signature.piop bodyA.2.2.1.1 e ≠ V.expand b.signature.piop bodyB.2.2.1.1 e →
        SlopeOutcome p randomCount enough V snapshot.world.other.family snapshot.world.other.hashTable
            (a.world.other.cipherHistory ++ b.world.other.cipherHistory) bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1 e ∨
          BranchEvent (tau := tau) snapshot.world.other.hashTable snapshot.input.payload.1 a.world.other ∨
          BranchEvent (tau := tau) snapshot.world.other.hashTable snapshot.input.payload.1 b.world.other ∨
          ¬ DigestCollisionFree snapshot.world.other.hashTable := by
  obtain ⟨left, right, a, b, hres, ha, hb, _, _, hai, hbi, _, _, hne⟩ :=
    SignatureReplayConsistency.successful_fork_attempts _ adversary snapshot result hr hw
  obtain ⟨hsnapW, hleftW, hrightW⟩ := SharedGameInvariant.fork_cutAt S V verifyBudget publicKey sampleWitness adversary
    index fuel c hc snapshot hsnap result hr left right hres
  obtain ⟨haW, haC⟩ := hleftW a ha
  obtain ⟨hbW, hbC⟩ := hrightW b hb
  -- The family is preserved along both branches.
  have hpF := SharedGameInvariant.shared_preserves S V verifyBudget publicKey sampleWitness
    (fun world => world.family = snapshot.world.other.family)
    (fun budget program world result hr hQ => (runProgram_family budget program world result hr).trans hQ)
  obtain ⟨hfamA, hfamB⟩ := SharedGameInvariant.fork_preserves _ _ hpF adversary snapshot rfl result hr left right hres
  -- Both attempts come from executed verifications.
  have hbranch : ∀ branch, branch ∈ (freshBranch (scheme (components S V verifyBudget publicKey sampleWitness)) adversary snapshot).support →
      ∀ att, branch.checked.terminal = .attempt att → att.world.other.family = snapshot.world.other.family →
      ∃ body recovered, att.signature.body = some body ∧
        Evaluates snapshot.world.other.family att.world.other.hashTable att.world.other.cipherHistory
          (verifyProgram V body.1 body.2.1 att.signature.piop body.2.2.1) (Except.ok recovered) ∧
        att.input.payload.1 = recovered.lines := by
    intro branch hbr att hatt hfam
    obtain ⟨wv, hwv⟩ := branch_attempt_source _ adversary snapshot branch hbr att hatt
    obtain ⟨body, recovered, hbody, heval, hlines, hfam'⟩ :=
      attempt_verification S V verifyBudget publicKey sampleWitness _ _ _ wv att.world att.input hwv
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
    intro e hdiff
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
    exact ForkSlopePrefix.fork_masked_slope_prefix xi p encode randomCount enough V hmid hencoding hlinesEnc
      bodyA.1 bodyB.1 bodyA.2.1 bodyB.2.1 a.signature.piop b.signature.piop bodyA.2.2.1 bodyB.2.2.1
      snapshot.world.other.family snapshot.world.other.hashTable a.world.other.hashTable b.world.other.hashTable
      haC.2 hbC.2 a.world.other.cipherHistory b.world.other.cipherHistory recA recB hevalA hevalB hinA hinB
      (by rw [← hlinesA, ← hlinesB, hai, hbi]) hfree e hdiff

end Shared

end
end SDitH.Proofs.ForkOutcome
