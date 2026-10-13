import SDitH.Proofs.CommitEntries
import SDitH.Proofs.TreeGoodInduction

/-! A stale last call forces the tree not to be good. The run before the
last call is the tree expansion continued by the commitment phase (the
commitments but the last, then the last leaf's first call); the
commitment phase records the other pairs' entries and the first call's
entry, at inputs that differ from the last call's input (other offsets,
or the same address with the other side), and the tree records inputs at
addresses below the leaf count; so an entry with the last call's key and
input lies in the starting history, which puts the last leaf's key among
the starting keys and the tree is not good. Hence the staleness event is
at most the not-good event of the tree's run. -/

namespace SDitH.Proofs.StaleNotGood

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open RowsSupport RunBind PrefixOrMention TreeRunEntries TreeStepFresh TreeGoodInduction HeadCommitSplit CommitEntries
open RowStoredPosterior RowStoredAfter CommitDecomposition
open scoped Classical ENNReal

noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The commitment phase from the tree: the commitments but the last, then
the last leaf's first call. -/
def commitPhase {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (nodes : Nat → Seed lambda) :
    SignerProgram lambda s wit rnd (BeforeData lambda tau kappa) :=
  Spec.HashCipherProgram.bind (collect (commitOf S.layout S.variant salt nodes)
      (Spec.SharedSlopeExec.allPairs tau kappa).dropLast fun _ => fun _ => false) fun acc' =>
    Program.cipher (.encrypt (lastKey (kappa := kappa) S.layout htau nodes)
        (S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) false))) fun left =>
      Program.done (nodes, acc', S.layout.output left)

theorem headBefore_eq {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) :
    headBefore htau S salt root = Spec.HashCipherProgram.bind
      (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) (commitPhase htau S salt) := rfl

/-- The commitment phase's budget. -/
def phaseBudget (tau kappa : Nat) : Nat := (Spec.SharedSlopeExec.allPairs tau kappa).dropLast.length * 2 + 1

theorem commitPhase_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (nodes : Nat → Seed lambda) :
    Bounded (phaseBudget tau kappa) (commitPhase htau S salt nodes) :=
  HashCipherProgram.bounded_bind _ _ _ 1
    (SharedSigner.collect_bounded _ 2 (fun _ => SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _)
    fun _ _ => trivial

theorem beforeBudget_eq (htau : tau ≠ 0) :
    beforeBudget tau kappa = 2 * (tau * 2 ^ kappa - 1) + phaseBudget tau kappa := by
  have := List.length_pos_of_ne_nil (allPairs_ne_nil (kappa := kappa) htau)
  unfold beforeBudget phaseBudget
  rw [List.length_dropLast]
  omega

/-- The run before the last call is the tree's run continued by the
commitment phase. -/
theorem runFixed_headBefore_split {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure family (beforeBudget tau kappa) (headBefore htau S salt root) table hashes ciphers log =
      (runFixed procedure family (2 * (tau * 2 ^ kappa - 1))
        (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) table hashes ciphers log).bind
        (continueRun family (phaseBudget tau kappa) (commitPhase htau S salt)) := by
  rw [beforeBudget_eq htau, headBefore_eq htau]
  exact runFixed_bind family _ _ _ _ (SharedSigner.treeThrough_bounded S.layout S.variant salt root (fun _ => root) _)
    (commitPhase_bounded htau S salt) table hashes ciphers log

/-- The first call's entry of the last leaf. -/
def leftEntry {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (nodes : Nat → Seed lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) : Spec.IdealCipher.Entry (Bits lambda) (Bits lambda) :=
  Spec.IdealCipher.entry (.encrypt (lastKey (kappa := kappa) S.layout htau nodes)
      (S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) false)))
    (family (lastKey (kappa := kappa) S.layout htau nodes)
      (S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) false)))

/-- The commitment phase's run from a tree: the data before the last call
and the recorded entries. -/
theorem commitPhase_support {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt : Bits lambda) (nodes : Nat → Seed lambda)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (BeforeData lambda tau kappa)))
    (hout : out ∈ (runFixed procedure family (phaseBudget tau kappa) (commitPhase htau S salt nodes)
      table hashes ciphers log).support) :
    (∃ acc' left, out.state = .done (nodes, acc', left)) ∧
      ∃ new, out.cipherHistory = leftEntry htau S salt nodes family :: (new ++ ciphers) ∧
        ∀ e ∈ new, CommitInput S.layout S.variant salt (Spec.SharedSlopeExec.allPairs tau kappa).dropLast e.input := by
  unfold commitPhase phaseBudget at hout
  have hp : Bounded ((Spec.SharedSlopeExec.allPairs tau kappa).dropLast.length * 2)
      (collect (commitOf (s := s) (wit := wit) (rnd := rnd) S.layout S.variant salt nodes)
        (Spec.SharedSlopeExec.allPairs tau kappa).dropLast fun _ => fun _ => false) :=
    SharedSigner.collect_bounded _ 2 (fun _ => SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _
  have hn : ∀ acc' : Fin tau × Fin (2 ^ kappa) → Digest lambda, Bounded 1
      (Program.cipher (.encrypt (lastKey (kappa := kappa) S.layout htau nodes)
        (S.layout.input (cipherInput S.variant salt (lastAddress (kappa := kappa) htau) false))) fun left =>
        (Program.done (nodes, acc', S.layout.output left) :
          SignerProgram lambda s wit rnd (BeforeData lambda tau kappa))) :=
    fun _ _ => trivial
  rw [runFixed_bind family _ 1 _ _ hp hn] at hout
  obtain ⟨mid, hmid, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨new, hnew, hform⟩ := commit_entries S.layout S.variant salt nodes family _ _ _ _ _ _ mid hmid
  obtain ⟨acc', hacc⟩ := runFixed_bounded_done family _ _
    (SharedSigner.collect_bounded _ 2 (fun pair => SharedSigner.commitCall_bounded S.layout _ S.variant salt _ _) _ _)
    _ _ _ _ mid hmid
  unfold continueRun at hcont
  rw [hacc] at hcont
  obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hcont
  simp only [runFixed, step_cipher, PMF.pure_bind, PMF.mem_support_pure_iff] at hinner
  subst hinner
  subst heq
  refine ⟨⟨acc', _, rfl⟩, new, ?_, hform⟩
  show _ :: mid.cipherHistory = _
  rw [hnew]
  rfl

/-- A stale last call puts the last leaf's key among the starting keys, so
the tree is not good. -/
theorem stale_notGood {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) (hin : Function.Injective S.layout.input)
    (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
    (treeOut : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Nat → Seed lambda)))
    (htree : treeOut ∈ (runFixed procedure family (2 * (tau * 2 ^ kappa - 1))
      (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) table hashes H log).support)
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (BeforeData lambda tau kappa)))
    (hout : out ∈ (continueRun family (phaseBudget tau kappa) (commitPhase htau S salt) treeOut).support)
    (hstale : staleOf htau S salt out = true) :
    notGood S.layout (keysOf H) (tau * 2 ^ kappa - 1) root treeOut = true := by
  obtain ⟨nodes, hnodes⟩ := runFixed_bounded_done family _ _
    (SharedSigner.treeThrough_bounded S.layout S.variant salt root (fun _ => root) _) _ _ _ _ treeOut htree
  obtain ⟨treeNew, htreeNew, htreeForm⟩ :=
    tree_entries S.layout S.variant salt root (fun _ => root) family _ table hashes H log treeOut htree
  unfold continueRun at hout
  rw [hnodes] at hout
  obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  obtain ⟨⟨acc', left, hstate⟩, new, hnew, hform⟩ := commitPhase_support htau S salt nodes family _ _ _ _ inner hinner
  subst heq
  have hstate' : staleOf htau S salt { inner with hashCollided := treeOut.hashCollided || inner.hashCollided } =
      stale htau S salt (nodes, acc', left) inner.cipherHistory := by
    unfold staleOf
    rw [show ({ inner with hashCollided := treeOut.hashCollided || inner.hashCollided } :
      Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
        (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (BeforeData lambda tau kappa))).state =
      inner.state from rfl, hstate]
  rw [hstate'] at hstale
  simp only [stale, decide_eq_true_eq] at hstale
  obtain ⟨e, he, hek, hei⟩ := hstale
  rw [hnew, htreeNew] at he
  have hlt : lastAddress (kappa := kappa) htau < 2 * (tau * 2 ^ kappa) := commit_address_lt _
  have hkeyH : lastKey (kappa := kappa) S.layout htau nodes ∈ keysOf H := by
    simp only [List.mem_cons, List.mem_append] at he
    rcases he with rfl | he | he | he
    · have := (SeedPrimitives.cipherInput_injective hl hL hlt hlt S.variant salt false true (hin hei)).2
      exact absurd this (by decide)
    · obtain ⟨pair, hpair, b, hx⟩ := hform e he
      rw [hx] at hei
      have hb := SeedPrimitives.cipherInput_injective hl hL (commit_address_lt pair) hlt S.variant salt b true (hin hei)
      have hoff := SeedTree.leafOffset_injective pair.1 (lastPair (kappa := kappa) htau).1 pair.2 (lastPair htau).2
        (by unfold lastAddress at hb; omega)
      exact absurd (Prod.ext hoff.1 hoff.2) (ne_lastPair_of_mem_dropLast htau pair hpair)
    · obtain ⟨i, b, hi, hik, hx⟩ := htreeForm e he
      rw [hx] at hei
      have hb := SeedPrimitives.cipherInput_injective hl hL (by omega) hlt S.variant salt b true (hin hei)
      have : tau * 2 ^ kappa ≤ lastAddress (kappa := kappa) htau := Nat.le_add_right _ _
      omega
    · exact mem_keysOf.mpr ⟨e, he, hek⟩
  unfold notGood treeOf
  rw [hnodes]
  simp only [decide_eq_true_eq]
  intro hgood
  have hb := (SeedTree.leafAddress_bounds (N := 2 ^ kappa) (lastPair (kappa := kappa) htau).1
    (lastPair (kappa := kappa) htau).2).2
  exact hgood (leafNode (lastPair (kappa := kappa) htau).1 (lastPair htau).2).val
    (by show Spec.SeedTree.leafAddress _ _ ≤ _; omega) hkeyH

/-- The staleness event's probability is at most the not-good event's. -/
theorem stale_le_notGood {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau] (htau : tau ≠ 0)
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) (hin : Function.Injective S.layout.input)
    (hl : 26 ≤ lambda) (hL : 4 * (tau * 2 ^ kappa) ≤ 2 ^ 24)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (H : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    ((runFixed procedure family (beforeBudget tau kappa) (headBefore htau S salt root) table hashes H log).map
        (staleOf htau S salt)) true ≤
      ((runFixed procedure family (2 * (tau * 2 ^ kappa - 1))
        (treeThrough S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) table hashes H log).map
        (notGood S.layout (keysOf H) (tau * 2 ^ kappa - 1) root)) true := by
  rw [runFixed_headBefore_split htau, PMF.map_bind]
  show _ ≤ ((runFixed procedure family _ _ table hashes H log).bind fun treeOut =>
    PMF.pure (notGood S.layout (keysOf H) (tau * 2 ^ kappa - 1) root treeOut)) true
  refine bind_true_le_bind_true _ _ _ fun treeOut htree => ?_
  refine (map_true_le_indicator _ _ (notGood S.layout (keysOf H) (tau * 2 ^ kappa - 1) root treeOut = true)
    fun out hout hstale => stale_notGood htau S salt root hin hl hL family table hashes H log treeOut htree out hout
      hstale).trans (le_of_eq ?_)
  rw [PMF.pure_apply]
  cases notGood S.layout (keysOf H) (tau * 2 ^ kappa - 1) root treeOut <;> simp [Spec.RandomOracleTrap.indicator]

end
end SDitH.Proofs.StaleNotGood
