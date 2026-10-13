import SDitH.Proofs.SharedSigning
import SDitH.Proofs.ForkCutRun
import SDitH.Proofs.SignatureReplayConsistency

/-! Invariants of the shared world along the abstract game. A predicate on
the other-state preserved by every service output is preserved by the
game's run and by the cut, so it holds at every attempt's world and at
every saved snapshot's world. The shared services preserve two such
predicates: well-formedness of the fresh-query log (traced, ordered,
fresh, extended and stored by the table) from the empty initial world,
and the cut at a fork table from a world extending that table. Hence the
snapshot's log is entirely pre-cut, and both branches' attempt worlds are
cut at the snapshot's shared table. -/

namespace SDitH.Proofs.SharedGameInvariant

open Spec.DomainSeparation Spec.SignatureSecurity Spec.AbstractSignature Spec.SignatureReplay Spec.RandomOracleTrace Spec.OracleChain
open Spec.SharedScheme Spec.SharedSigning Spec.HashCipherProgram
open Spec.PIOPArithmetic (selectorCount)
open Spec.SlopeConsistencyGame (Out)
open ForkCut (Cut)
open ForkCutRun (PreCut)
open scoped Classical
noncomputable section

section Generic

variable {PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer State : Type*}
variable [Fintype Digest] [Nonempty Digest]

/-- The scheme's services preserve a predicate on the other-state. -/
structure Preserves (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
    (Q : Other → Prop) : Prop where
  prepare : ∀ pk sk msg other r, r ∈ (components.prepareSigning pk sk msg other).support → Q other → Q r.2.2
  open_ : ∀ st d other r, r ∈ (components.openSigning st d other).support → Q other → Q r.2
  verify : ∀ pk msg sig other r, r ∈ (components.prepareVerification pk msg sig other).support → Q other → Q r.2
  oracle : ∀ q other r, r ∈ (components.publicOracle q other).support → Q other → Q r.2

variable (components : Components PublicKey SecretKey Message Payload Digest Body CommitState Other Query Answer)
  (Q : Other → Prop)

theorem sign_preserves (hp : Preserves components Q) (sk : PublicKey × SecretKey) (message : Message)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (r : Signature Digest Body × World (HashInput PublicKey Message Payload) Digest Other)
    (hr : r ∈ ((scheme components).sign sk message world).support) (hQ : Q world.other) : Q r.2.other := by
  obtain ⟨prepared, hprep, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
  obtain ⟨hashed, _, hopen⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  obtain ⟨opened, hopened, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hopen
  subst hres
  exact hp.open_ _ _ _ opened hopened (hp.prepare _ _ _ _ prepared hprep hQ)

theorem verify_preserves (hp : Preserves components Q) (pk : PublicKey) (message : Message) (signature : Signature Digest Body)
    (world : World (HashInput PublicKey Message Payload) Digest Other)
    (r : Option (HashInput PublicKey Message Payload) × World (HashInput PublicKey Message Payload) Digest Other)
    (hr : r ∈ ((scheme components).prepareVerification pk message signature world).support) (hQ : Q world.other) :
    Q r.2.other := by
  obtain ⟨result, hresult, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  subst hres
  exact hp.verify _ _ _ _ result hresult hQ

theorem oracle_preserves (hp : Preserves components Q) (query : Query) (world : World (HashInput PublicKey Message Payload) Digest Other)
    (r : Answer × World (HashInput PublicKey Message Payload) Digest Other)
    (hr : r ∈ ((scheme components).publicOracle query world).support) (hQ : Q world.other) : Q r.2.other := by
  obtain ⟨result, hresult, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  subst hres
  exact hp.oracle _ _ result hresult hQ

/-- Along the run, every attempt's world satisfies the predicate. -/
theorem run_preserves (hp : Preserves components Q) (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State) :
    ∀ (fuel : Nat) (pk : PublicKey) (sk : PublicKey × SecretKey) (state : State)
      (world : World (HashInput PublicKey Message Payload) Digest Other)
      (trace : Trace Message (HashInput PublicKey Message Payload) Query)
      (terminal : Terminal Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query),
      terminal ∈ (Spec.SignatureSecurity.run (scheme components) adversary fuel pk sk state world trace).support → Q world.other →
      ∀ a, terminal = .attempt a → Q a.world.other := by
  intro fuel
  induction fuel with
  | zero =>
    intro pk sk state world trace terminal ht _ a ha
    simp only [Spec.SignatureSecurity.run, PMF.mem_support_pure_iff] at ht
    subst ht
    cases ha
  | succ fuel ih =>
    intro pk sk state world trace terminal ht hQ a ha
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
      have hQ' := verify_preserves components Q hp pk message signature world result hresult hQ
      cases hopt : result.1 with
      | none =>
        rw [hopt] at ha
        cases ha
      | some input =>
        rw [hopt] at ha
        cases ha
        exact hQ'
    | sign message next =>
      obtain ⟨result, hresult, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih pk sk _ _ _ terminal hrun (sign_preserves components Q hp sk message world result hresult hQ) a ha
    | hash input next =>
      obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih pk sk _ _ _ terminal hrun hQ a ha
    | query input next =>
      obtain ⟨result, hresult, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih pk sk _ _ _ terminal hrun (oracle_preserves components Q hp input world result hresult hQ) a ha

/-- Along the cut, every saved snapshot's world and every attempt's world
satisfies the predicate. -/
theorem cut_preserves (hp : Preserves components Q) (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State) :
    ∀ (index fuel : Nat) (pk : PublicKey) (sk : PublicKey × SecretKey) (state : State)
      (world : World (HashInput PublicKey Message Payload) Digest Other)
      (trace : Trace Message (HashInput PublicKey Message Payload) Query)
      (c : Spec.SignatureReplay.Cut PublicKey (PublicKey × SecretKey) Message (Signature Digest Body)
        (HashInput PublicKey Message Payload) Digest Other Query State),
      c ∈ (Spec.SignatureReplay.cut (scheme components) adversary index fuel pk sk state world trace).support →
      Q world.other →
      (∀ snapshot, c = .saved snapshot → Q snapshot.world.other) ∧
      ∀ a, c = .ended (.attempt a) → Q a.world.other := by
  intro index fuel
  induction fuel generalizing index with
  | zero =>
    intro pk sk state world trace c hc _
    simp only [Spec.SignatureReplay.cut, PMF.mem_support_pure_iff] at hc
    subst hc
    exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | succ fuel ih =>
    intro pk sk state world trace c hc hQ
    simp only [Spec.SignatureReplay.cut] at hc
    obtain ⟨action, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
    cases action with
    | abort =>
      simp only [PMF.mem_support_pure_iff] at hrest
      subst hrest
      exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    | finish message signature =>
      obtain ⟨result, hresult, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
      subst hres
      have hQ' := verify_preserves components Q hp pk message signature world result hresult hQ
      refine ⟨(fun _ h => nomatch h), fun a ha => ?_⟩
      cases hopt : result.1 with
      | none =>
        rw [hopt] at ha
        cases ha
      | some input =>
        rw [hopt] at ha
        cases ha
        exact hQ'
    | sign message next =>
      obtain ⟨result, hresult, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih index pk sk _ _ _ c hrun (sign_preserves components Q hp sk message world result hresult hQ)
    | hash input next =>
      cases index with
      | zero =>
        simp only [PMF.mem_support_pure_iff] at hrest
        subst hrest
        exact ⟨(fun snapshot h => by cases h; exact hQ), (fun _ h => nomatch h)⟩
      | succ index =>
        obtain ⟨result, _, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
        exact ih index pk sk _ _ _ c hrun hQ
    | query input next =>
      obtain ⟨result, hresult, hrun⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
      exact ih index pk sk _ _ _ c hrun (oracle_preserves components Q hp input world result hresult hQ)

theorem finalize_terminal (terminal : Terminal Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (checked : Checked Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (h : checked ∈ (finalize terminal).support) : checked.terminal = terminal := by
  cases terminal with
  | attempt a =>
    simp only [finalize] at h
    obtain ⟨_, _, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    rw [← hres]
  | exhausted t =>
    simp only [finalize, PMF.mem_support_pure_iff] at h
    subst h
    rfl
  | aborted t =>
    simp only [finalize, PMF.mem_support_pure_iff] at h
    subst h
    rfl
  | rejected t =>
    simp only [finalize, PMF.mem_support_pure_iff] at h
    subst h
    rfl

/-- Both branches of a fork at a snapshot satisfy the predicate at their
attempts, given the snapshot's world does. -/
theorem fork_preserves (hp : Preserves components Q) (adversary : Adversary PublicKey Message (Signature Digest Body)
      (HashInput PublicKey Message Payload) Digest Query Answer State)
    (snapshot : Snapshot PublicKey (PublicKey × SecretKey) Message (HashInput PublicKey Message Payload) Digest Other Query State)
    (hQ : Q snapshot.world.other)
    (result : Option (Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query ×
      Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query))
    (hr : result ∈ (forkAt (scheme components) adversary snapshot).support)
    (left right : Branch Message (Signature Digest Body) (HashInput PublicKey Message Payload) Digest Other Query)
    (hres : result = some (left, right)) :
    (∀ a, left.checked.terminal = .attempt a → Q a.world.other) ∧
      ∀ b, right.checked.terminal = .attempt b → Q b.world.other := by
  have hbranch : ∀ branch, branch ∈ (freshBranch (scheme components) adversary snapshot).support →
      ∀ a, branch.checked.terminal = .attempt a → Q a.world.other := by
    intro branch hb a ha
    obtain ⟨answer, _, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
    obtain ⟨checked, hchecked, hbr⟩ := (PMF.mem_support_map_iff _ _ _).mp hcont
    subst hbr
    obtain ⟨terminal, hterm, hfin⟩ := (PMF.mem_support_bind_iff _ _ _).mp hchecked
    have hwin := run_preserves components Q hp adversary snapshot.remaining snapshot.publicKey snapshot.secretKey
      (snapshot.next answer) _ _ terminal hterm hQ a
    exact hwin ((finalize_terminal terminal checked hfin).symm.trans ha)
  cases he : snapshot.world.hashTable snapshot.input with
  | some _ =>
    simp only [forkAt, he, PMF.mem_support_pure_iff] at hr
    subst hr
    cases hres
  | none =>
    rw [forkAt, he] at hr
    obtain ⟨l, hl, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨r, hr', hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
    rw [← hpair] at hres
    cases hres
    exact ⟨hbranch _ hl, hbranch _ hr'⟩

end Generic

section Shared

variable {lambda tau kappa s higherCount r k w wpow : Nat} {widths : List Nat}
variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- The fresh-query log is traced, ordered, fresh, and extended and stored by the table. -/
def WellFormed {wit rnd : Nat} (world : Spec.SharedScheme.World lambda s wit rnd) : Prop :=
  Traced world.hashTable world.trace ∧ Ordered world.trace ∧ Fresh world.trace ∧
    (∀ entry ∈ world.trace, Extends entry.before world.hashTable) ∧
    ∀ entry ∈ world.trace, world.hashTable entry.input = some entry.answer

/-- The log is cut at a fork table that the current table extends. -/
def CutAt {wit rnd : Nat} (P : List Bool → Option (Out lambda s wit rnd)) (world : Spec.SharedScheme.World lambda s wit rnd) : Prop :=
  Cut P world.trace ∧ Extends P world.hashTable

theorem runProgram_wellFormed {A : Type*} {wit rnd : Nat} (budget : Nat)
    (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (result : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd)
    (hr : result ∈ (runProgram budget program world).support) (hw : WellFormed world) : WellFormed result.2 := by
  obtain ⟨out, hout, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  subst hres
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := HashCipherTrace.run_invariants procedure world.family budget program world.hashTable
    world.hashHistory world.cipherHistory world.trace out hout hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2
  exact ⟨h1, h2, h3, h4, h5⟩

theorem runProgram_cutAt {A : Type*} {wit rnd : Nat} (P : List Bool → Option (Out lambda s wit rnd)) (budget : Nat)
    (program : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A)
    (world : Spec.SharedScheme.World lambda s wit rnd)
    (result : Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) A × Spec.SharedScheme.World lambda s wit rnd)
    (hr : result ∈ (runProgram budget program world).support) (hc : CutAt P world) : CutAt P result.2 := by
  obtain ⟨out, hout, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  subst hres
  exact ForkCutRun.run_cut procedure world.family P budget program world.hashTable world.hashHistory
    world.cipherHistory world.trace out hout hc.1 hc.2

/-- A predicate preserved by every program run is preserved by the shared services. -/
theorem shared_preserves [NeZero tau] [DecidableEq F]
    (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
    (verifyBudget : Nat) (publicKey : List Bool) (sampleWitness : PMF (Fin (selectorCount widths * w) → ZMod 2))
    (Q : Spec.SharedScheme.World lambda s (selectorCount widths * w) (lambda * (widths.length - 1)) → Prop)
    (hrun : ∀ {A : Type} (budget : Nat)
      (program : Program (List Bool) (Out lambda s (selectorCount widths * w) (lambda * (widths.length - 1))) (Bits lambda) (Bits lambda) A)
      world result, result ∈ (runProgram budget program world).support → Q world → Q result.2) :
    Preserves (components S V verifyBudget publicKey sampleWitness) Q where
  prepare := by
    intro pk sk msg other r hr hQ
    obtain ⟨salt, _, hsalt⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    obtain ⟨root, _, hroot⟩ := (PMF.mem_support_bind_iff _ _ _).mp hsalt
    obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hroot
    have hQ' := hrun _ _ other run hrun' hQ
    rw [← hres]
    cases run.1 <;> exact hQ'
  open_ := by
    intro st d other r hr hQ
    simp only [components, openSigning, PMF.mem_support_pure_iff] at hr
    subst hr
    exact hQ
  verify := by
    intro pk msg sig other r hr hQ
    change r ∈ (Spec.SharedSigning.prepareVerification S V verifyBudget pk msg sig other).support at hr
    unfold Spec.SharedSigning.prepareVerification at hr
    rcases hbody : sig.body with _ | body
    · rw [hbody] at hr
      simp only [PMF.mem_support_pure_iff] at hr
      subst hr
      exact hQ
    · rw [hbody] at hr
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact hrun _ _ other run hrun' hQ
  oracle := by
    intro q other r hr hQ
    cases q with
    | hash input =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact hrun _ _ other run hrun' hQ
    | mask input =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact hrun _ _ other run hrun' hQ
    | cipher request =>
      obtain ⟨run, hrun', hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      subst hres
      exact hrun _ _ other run hrun' hQ

theorem keygen_wellFormed {wit rnd : Nat} (publicKey : List Bool) (sampleWitness : PMF (Fin wit → ZMod 2))
    (generated : List Bool × (Fin wit → ZMod 2) × Spec.SharedScheme.World lambda s wit rnd)
    (hg : generated ∈ (keygen publicKey sampleWitness).support) : WellFormed generated.2.2 := by
  obtain ⟨witness, _, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg
  obtain ⟨family, _, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hrest
  subst hres
  refine ⟨⟨(fun _ _ h => nomatch h), (fun _ h => nomatch h)⟩, ?_, ?_, ?_, ?_⟩
  · intro i j hi; simp at hi
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

/-- A well-formed world is pre-cut at its own table, hence cut at it. -/
theorem wellFormed_preCut {wit rnd : Nat} (world : Spec.SharedScheme.World lambda s wit rnd) (hw : WellFormed world) :
    PreCut world.hashTable world.trace :=
  fun entry hentry => ⟨hw.2.2.2.1 entry hentry, hw.2.2.2.2 entry hentry⟩

theorem wellFormed_cutAt {wit rnd : Nat} (world : Spec.SharedScheme.World lambda s wit rnd) (hw : WellFormed world) :
    CutAt world.hashTable world :=
  ⟨ForkCutRun.cut_of_preCut _ _ (wellFormed_preCut world hw), RandomOracleTrace.extends_refl _⟩

/-- At a saved snapshot of the shared game, the world is well formed; both
branches' attempt worlds are well formed and cut at the snapshot's table. -/
theorem fork_cutAt [NeZero tau] [DecidableEq F]
    (S : SigningSetting F lambda tau kappa s r k w wpow higherCount widths)
    (V : VerifierSetting F lambda tau kappa s (selectorCount widths * w) (lambda * (widths.length - 1)))
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
    (left right) (hres : result = some (left, right)) :
    WellFormed snapshot.world.other ∧
      (∀ a, left.checked.terminal = .attempt a → WellFormed a.world.other ∧ CutAt snapshot.world.other.hashTable a.world.other) ∧
      ∀ b, right.checked.terminal = .attempt b → WellFormed b.world.other ∧ CutAt snapshot.world.other.hashTable b.world.other := by
  have hpW := shared_preserves S V verifyBudget publicKey sampleWitness WellFormed
    (fun budget program world result hr hQ => runProgram_wellFormed budget program world result hr hQ)
  obtain ⟨generated, hgen, hrest⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
  obtain ⟨state, _, hcut⟩ := (PMF.mem_support_bind_iff _ _ _).mp hrest
  have hinit : WellFormed generated.2.2.other := by
    obtain ⟨g, hg, hgen'⟩ := (PMF.mem_support_map_iff _ _ _).mp hgen
    subst hgen'
    exact keygen_wellFormed publicKey sampleWitness g hg
  have hsnapW := (cut_preserves _ WellFormed hpW adversary index fuel _ _ state _ _ c hcut hinit).1 snapshot hsnap
  have hpC := shared_preserves S V verifyBudget publicKey sampleWitness (CutAt snapshot.world.other.hashTable)
    (fun budget program world result hr hQ => runProgram_cutAt _ budget program world result hr hQ)
  have hforkW := fork_preserves _ WellFormed hpW adversary snapshot hsnapW result hr left right hres
  have hforkC := fork_preserves _ (CutAt snapshot.world.other.hashTable) hpC adversary snapshot
    (wellFormed_cutAt _ hsnapW) result hr left right hres
  exact ⟨hsnapW, fun a ha => ⟨hforkW.1 a ha, hforkC.1 a ha⟩, fun b hb => ⟨hforkW.2 b hb, hforkC.2 b hb⟩⟩

end Shared

end
end SDitH.Proofs.SharedGameInvariant
