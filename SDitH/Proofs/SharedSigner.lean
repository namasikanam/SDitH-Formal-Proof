import SDitH.Spec.SharedSigner
import SDitH.Proofs.HashCipherEvaluation
import SDitH.Proofs.HashCipherProgram
import SDitH.Proofs.SharedSlopeExec

/-! A successful evaluation of the honest signer's commitment program is
Algorithm 7's commitment under the primitives induced by the executed
family and table, with every chain query recorded: the row, outer,
auxiliary, mask and lines lookups are stored, both commitment calls of every
leaf seed are in the cipher history, and the result's fields are the commit
arithmetic at the stored mask. The program is bounded by `commitBudget`. -/

namespace SDitH.Proofs.SharedSigner

open Spec.BAVC Spec.DomainSeparation Spec.BAVCChainInputs Spec.HashCipherProgram Spec.HashCipherEvaluation
open Spec.SeedPrimitives Spec.SharedSigner
open Spec.SlopeConsistencyGame (Out Mask)
noncomputable section

variable {lambda tau kappa s wit rnd : Nat}

/-- The digest component stored at an input, default outside the table. -/
def digestAt (table : List Bool → Option (Out lambda s wit rnd)) (x : List Bool) : Digest lambda :=
  match table x with
  | some pair => pair.1
  | none => fun _ => false

theorem digestAt_of_stored (table : List Bool → Option (Out lambda s wit rnd)) (x : List Bool)
    (pair : Out lambda s wit rnd) (h : table x = some pair) : digestAt table x = pair.1 := by
  simp [digestAt, h]

variable (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
  (table : List Bool → Option (Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))

/-- Both cipher entries of an ExpandSeed call at a layout. -/
def expandEntries (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (address : Nat) (seed : Bits lambda) : Prop :=
  ∀ side : Bool,
    Spec.IdealCipher.entry (.encrypt (layout.key seed) (layout.input (cipherInput variant salt address side)))
      (family (layout.key seed) (layout.input (cipherInput variant salt address side))) ∈ ciphers

theorem expandCall_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt : Bits lambda) (address : Nat) (seed : Bits lambda) (value : Bits lambda × Bits lambda)
    (h : Evaluates family table ciphers (expandCall (s := s) (wit := wit) (rnd := rnd) layout variant salt address seed) value) :
    value = expandSeed variant (Spec.BAVCCipherProgram.encStar layout family) salt address seed ∧
      expandEntries family ciphers layout variant salt address seed := by
  cases h with
  | cipher _ _ _ left tail =>
    cases tail with
    | cipher _ _ _ right tail =>
      cases tail
      refine ⟨rfl, fun side => ?_⟩
      cases side
      · exact left
      · exact right

theorem commitCall_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (leafCount : Nat) (variant : Grinding) (salt seed : Bits lambda) (index : Nat) (value : Digest lambda)
    (h : Evaluates family table ciphers
      (commitCall (s := s) (wit := wit) (rnd := rnd) layout leafCount variant salt seed index) value) :
    value = commitSeed leafCount variant (Spec.BAVCCipherProgram.encStar layout family) salt seed index ∧
      expandEntries family ciphers layout variant salt (leafCount + index) seed := by
  obtain ⟨pair, hpair, hv⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp h
  obtain ⟨rfl, hentries⟩ := expandCall_evaluates family table ciphers layout variant salt _ seed pair hpair
  cases hv
  exact ⟨rfl, hentries⟩

theorem treeThrough_evaluates (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt root : Bits lambda) (initial : Nat → Seed lambda) (steps : Nat)
    (value : Nat → Seed lambda)
    (h : Evaluates family table ciphers
      (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root initial steps) value) :
    value = Spec.SeedTree.run (expandSeed variant (Spec.BAVCCipherProgram.encStar layout family) salt) root initial steps := by
  induction steps generalizing value with
  | zero =>
    cases h
    rfl
  | succ steps ih =>
    obtain ⟨tree, htree, hv⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp h
    obtain ⟨children, hchildren, hdone⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp hv
    obtain ⟨rfl, _⟩ := expandCall_evaluates family table ciphers layout variant salt _ _ children hchildren
    cases hdone
    rw [ih tree htree]
    rfl

theorem collect_evaluates {ι B : Type*} [DecidableEq ι] (call : ι → SignerProgram lambda s wit rnd B)
    (f : ι → B) (P : ι → Prop) (hcall : ∀ k v, Evaluates family table ciphers (call k) v → v = f k ∧ P k)
    (l : List ι) (acc : ι → B) (value : ι → B) (h : Evaluates family table ciphers (collect call l acc) value) :
    (∀ k ∈ l, value k = f k ∧ P k) ∧ ∀ k ∉ l, value k = acc k := by
  induction l generalizing acc with
  | nil =>
    cases h
    exact ⟨fun k hk => absurd hk (List.not_mem_nil), fun _ _ => rfl⟩
  | cons k rest ih =>
    obtain ⟨middle, hmid, hrest⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp h
    obtain ⟨rfl, hP⟩ := hcall k middle hmid
    obtain ⟨hin, hout⟩ := ih _ hrest
    refine ⟨fun k' hk' => ?_, fun k' hk' => ?_⟩
    · by_cases hr : k' ∈ rest
      · exact hin k' hr
      · have hk : k' = k := by
          rcases List.mem_cons.mp hk' with h | h
          · exact h
          · exact absurd h hr
        subst hk
        rw [hout k' hr, Function.update_self]
        exact ⟨rfl, hP⟩
    · have hne : k' ≠ k := fun h => hk' (h ▸ List.mem_cons_self)
      have hr : k' ∉ rest := fun h => hk' (List.mem_cons_of_mem k h)
      rw [hout k' hr, Function.update_of_ne hne]

theorem hashCall_evaluates (input : List Bool) (value : Digest lambda)
    (h : Evaluates family table ciphers (hashCall (s := s) (wit := wit) (rnd := rnd) input) value) :
    value = digestAt table input ∧ ∃ pair, table input = some pair := by
  cases h with
  | hash _ _ answer _ stored tail =>
    cases tail
    exact ⟨(digestAt_of_stored table input answer stored).symm, answer, stored⟩

/-- The BAVC primitives induced by the executed family and table. -/
def inducedPrimitives (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding) :
    Primitives lambda :=
  bavcPrimitives (tau * 2 ^ kappa) variant (Spec.BAVCCipherProgram.encStar layout family) (digestAt table)

/-- A successful evaluation of the commitment program is Algorithm 7's
commitment under the induced primitives, with every chain query recorded. -/
theorem commit_evaluates {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) (witness : Fin wit → ZMod 2)
    (value : Committed F lambda tau kappa s wit rnd)
    (h : Evaluates family table ciphers (commitProgram S salt root witness) value) :
    let bavc := Spec.BAVC.commit (inducedPrimitives (tau := tau) (kappa := kappa) family table S.layout S.variant) salt root
    let random := Spec.BLCCommit.randomTable S.p salt bavc.seeds S.randomCount S.enough
    let corrections := Spec.BLCCommit.positiveCorrections (Spec.BLC.correction Spec.GrayCode.grayFieldRow random)
    let arithmetic := Spec.BLC.commitArithmetic S.xi Spec.GrayCode.grayFieldRow random value.mask witness
    value.seeds = bavc.seeds ∧ value.result.key = bavc.key ∧ value.hcom = bavc.hcom ∧
      (∀ e, ∃ pair, table (Spec.BAVCBinding.rowQuery bavc.key.commitments e) = some pair ∧ pair.1 = value.rowHashes e) ∧
      (∃ pair, table (outerString salt value.rowHashes) = some pair ∧ pair.1 = value.hcom) ∧
      (∃ pair, table (Spec.BLCHashChain.auxQuery value.hcom (Spec.BLCHashChain.sourceTail S.encoding corrections)) = some pair ∧
        pair.1 = value.auxiliary) ∧
      (∃ pair, table (maskInput value.auxiliary) = some pair ∧ pair.2 = value.mask) ∧
      (∃ pair, table (Spec.BLCHashChain.linesQuery value.auxiliary
        (S.linesTail arithmetic.plainCheck arithmetic.baseCheck arithmetic.witnessCorrection)) = some pair ∧
        pair.1 = value.result.lines) ∧
      value.result.witness = arithmetic.witnessLines ∧ value.result.randomness = arithmetic.randomnessLines ∧
      value.result.auxiliary = ⟨corrections, arithmetic.plainCheck, arithmetic.witnessCorrection⟩ ∧
      ∀ e i, expandEntries family ciphers S.layout S.variant salt (tau * 2 ^ kappa + Spec.SeedTree.leafOffset e i)
        (bavc.seeds e i) := by
  intro bavc random corrections arithmetic
  obtain ⟨nodes, hnodes, h1⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp h
  obtain ⟨commits, hcommits, h2⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp h1
  obtain ⟨rowHashes, hrows, h3⟩ := (HashCipherEvaluation.evaluates_bind family table ciphers _ _ value).mp h2
  have htree := treeThrough_evaluates family table ciphers S.layout S.variant salt root _ _ nodes hnodes
  subst htree
  have hseeds : (fun e i => Spec.SeedTree.run (expandSeed S.variant (Spec.BAVCCipherProgram.encStar S.layout family) salt)
      root (fun _ => root) (tau * 2 ^ kappa - 1) (leafNode e i).val) = bavc.seeds := rfl
  obtain ⟨hcin, _⟩ := collect_evaluates family table ciphers _
    (fun pair : Fin tau × Fin (2 ^ kappa) => commitSeed (tau * 2 ^ kappa) S.variant
      (Spec.BAVCCipherProgram.encStar S.layout family) salt (bavc.seeds pair.1 pair.2) (Spec.SeedTree.leafOffset pair.1 pair.2))
    (fun pair => expandEntries family ciphers S.layout S.variant salt
      (tau * 2 ^ kappa + Spec.SeedTree.leafOffset pair.1 pair.2) (bavc.seeds pair.1 pair.2))
    (fun pair v hv => commitCall_evaluates family table ciphers S.layout _ S.variant salt _ _ v hv)
    _ _ commits hcommits
  have hcommitments : (fun e i => commits (e, i)) = bavc.key.commitments := by
    funext e i
    exact (hcin (e, i) (SharedSlopeExec.mem_allPairs e i)).1
  obtain ⟨hrin, _⟩ := collect_evaluates family table ciphers _
    (fun e => digestAt table (Spec.BAVCBinding.rowQuery (fun e i => commits (e, i)) e))
    (fun e => ∃ pair, table (Spec.BAVCBinding.rowQuery (fun e i => commits (e, i)) e) = some pair)
    (fun e v hv => hashCall_evaluates family table ciphers _ v hv) _ _ rowHashes hrows
  cases h3 with
  | hash _ _ outer _ houter h4 =>
    cases h4 with
    | hash _ _ auxiliary _ haux h5 =>
      cases h5 with
      | hash _ _ maskAnswer _ hmask h6 =>
        cases h6 with
        | hash _ _ lines _ hlines h7 =>
          cases h7
          have hrowfun : rowHashes = fun e => digestAt table (Spec.BAVCBinding.rowQuery bavc.key.commitments e) := by
            funext e
            rw [(hrin e (List.mem_finRange e)).1, hcommitments]
          refine ⟨rfl, ?_, ?_, ?_, ⟨outer, houter, rfl⟩, ⟨auxiliary, haux, rfl⟩, ⟨maskAnswer, hmask, rfl⟩,
            ⟨lines, hlines, rfl⟩, rfl, rfl, rfl, fun e i => (hcin (e, i) (SharedSlopeExec.mem_allPairs e i)).2⟩
          · show (⟨_, fun e i => commits (e, i)⟩ : Key lambda tau (2 ^ kappa)) = bavc.key
            rw [hcommitments]
            rfl
          · show outer.1 = bavc.hcom
            rw [← digestAt_of_stored table _ outer houter, hrowfun]
            rfl
          · intro e
            obtain ⟨pair, hpair⟩ := (hrin e (List.mem_finRange e)).2
            rw [hcommitments] at hpair
            refine ⟨pair, hpair, ?_⟩
            show pair.1 = rowHashes e
            rw [(hrin e (List.mem_finRange e)).1, hcommitments, digestAt_of_stored table _ pair hpair]

theorem expandCall_bounded (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt : Bits lambda) (address : Nat) (seed : Bits lambda) :
    Bounded 2 (expandCall (s := s) (wit := wit) (rnd := rnd) layout variant salt address seed) := by
  intro _ _
  trivial

theorem commitCall_bounded (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (leafCount : Nat) (variant : Grinding) (salt seed : Bits lambda) (index : Nat) :
    Bounded 2 (commitCall (s := s) (wit := wit) (rnd := rnd) layout leafCount variant salt seed index) :=
  HashCipherProgram.bounded_bind _ _ 2 0 (expandCall_bounded layout variant salt _ seed) fun _ => trivial

theorem treeThrough_bounded (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt root : Bits lambda) (initial : Nat → Seed lambda) (steps : Nat) :
    Bounded (2 * steps) (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root initial steps) := by
  induction steps with
  | zero => trivial
  | succ steps ih =>
    have := HashCipherProgram.bounded_bind _ _ (2 * steps) 2 ih fun tree =>
      HashCipherProgram.bounded_bind _ (fun children => Program.done (Function.update
          (Function.update tree (2 * (steps + 1)) children.1) (2 * (steps + 1) + 1) children.2)) 2 0
        (expandCall_bounded layout variant salt (steps + 1) (tree (steps + 1))) fun _ => trivial
    exact HashCipherProgram.bounded_mono _ _ _ (by omega) this

theorem collect_bounded {ι B : Type*} [DecidableEq ι] (call : ι → SignerProgram lambda s wit rnd B) (k : Nat)
    (hcall : ∀ i, Bounded k (call i)) (l : List ι) (acc : ι → B) :
    Bounded (l.length * k) (collect call l acc) := by
  induction l generalizing acc with
  | nil =>
    rw [List.length_nil, Nat.zero_mul]
    trivial
  | cons i rest ih =>
    have := HashCipherProgram.bounded_bind _ _ k (rest.length * k) (hcall i) fun value => ih (Function.update acc i value)
    exact HashCipherProgram.bounded_mono _ _ _ (by simp [List.length_cons, Nat.succ_mul]; omega) this

theorem hashCall_bounded (input : List Bool) : Bounded 1 (hashCall (s := s) (wit := wit) (rnd := rnd) (lambda := lambda) input) := by
  intro _
  trivial

theorem commit_bounded {F : Type*} [Field F] [Algebra (ZMod 2) F] [NeZero tau]
    (S : SignerSetting F lambda tau kappa s wit rnd) (salt root : Bits lambda) (witness : Fin wit → ZMod 2) :
    Bounded (commitBudget tau kappa) (commitProgram S salt root witness) := by
  unfold commitProgram commitBudget
  refine HashCipherProgram.bounded_mono _ _ _ (by omega)
    (HashCipherProgram.bounded_bind _ _ (2 * (tau * 2 ^ kappa - 1))
      (2 * (Spec.SharedSlopeExec.allPairs tau kappa).length + (tau + 4))
      (treeThrough_bounded S.layout S.variant salt root (fun _ => root) (tau * 2 ^ kappa - 1)) fun nodes => ?_)
  refine HashCipherProgram.bounded_mono _ _ _ (by rw [Nat.mul_comm])
    (HashCipherProgram.bounded_bind _ _ ((Spec.SharedSlopeExec.allPairs tau kappa).length * 2) (tau + 4)
      (collect_bounded _ 2 (fun pair => commitCall_bounded S.layout _ S.variant salt _ _) _ _) fun commits => ?_)
  refine HashCipherProgram.bounded_mono _ _ _ (by simp [List.length_finRange])
    (HashCipherProgram.bounded_bind _ _ ((List.finRange tau).length * 1) 4
      (collect_bounded _ 1 (fun e => hashCall_bounded _) _ _) fun rowHashes => ?_)
  intro _ _ _ _
  trivial

end
end SDitH.Proofs.SharedSigner
