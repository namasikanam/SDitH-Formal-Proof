import SDitH.Proofs.RowsSupport
import SDitH.Proofs.SharedResample
import SDitH.Proofs.HeadCommitSplit

/-! The tree expansion's run, step by step. The tree expansion through one
more step is the expansion so far bound to the node's expansion step (both
cipher calls, then the children's update), so its traced run with the
doubled budget is the run so far continued by the step's run; an
expansion step's run records exactly the two calls' entries and finishes
with the updated tree; and every entry the tree expansion records has as
input the layout's input of a cipher input at an address within the
expanded range. -/

namespace SDitH.Proofs.TreeRunEntries

open Spec.BAVC Spec.DomainSeparation Spec.HashCipherProgram Spec.SharedSigner Spec.SeedPrimitives Spec.HashCipherTrace
open Spec.SlopeConsistencyGame (Out)
open RowsSupport RunBind PrefixOrMention
open scoped Classical

noncomputable section

variable {lambda s wit rnd : Nat}

/-- The expansion step at a node: both calls, then the children's update. -/
def expandStep (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (k : Nat) (tree : Nat → Seed lambda) : SignerProgram lambda s wit rnd (Nat → Seed lambda) :=
  Spec.HashCipherProgram.bind (expandCall layout variant salt (k + 1) (tree (k + 1))) fun children =>
    Program.done (Function.update (Function.update tree (2 * (k + 1)) children.1) (2 * (k + 1) + 1) children.2)

theorem treeThrough_succ (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (initial : Nat → Seed lambda) (k : Nat) :
    treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root initial (k + 1) =
      Spec.HashCipherProgram.bind (treeThrough layout variant salt root initial k) (expandStep layout variant salt k) := rfl

theorem expandStep_bounded (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (k : Nat) (tree : Nat → Seed lambda) :
    Bounded 2 (expandStep (s := s) (wit := wit) (rnd := rnd) layout variant salt k tree) :=
  HashCipherProgram.bounded_bind _ _ 2 0 (SharedSigner.expandCall_bounded layout variant salt _ _) fun _ => trivial

/-- The tree expansion's run through one more step is the run so far
continued by the step's run. -/
theorem runFixed_tree_succ (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (initial : Nat → Seed lambda) (k : Nat)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd))) :
    runFixed procedure family (2 * (k + 1)) (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root initial (k + 1))
        table hashes ciphers log =
      (runFixed procedure family (2 * k) (treeThrough layout variant salt root initial k) table hashes ciphers log).bind
        (continueRun family 2 (expandStep layout variant salt k)) := by
  rw [treeThrough_succ, show 2 * (k + 1) = 2 * k + 2 by ring]
  exact runFixed_bind family (2 * k) 2 _ _ (SharedSigner.treeThrough_bounded layout variant salt root initial k)
    (fun _ => expandStep_bounded layout variant salt k _) table hashes ciphers log

/-- An expansion call bound to a pure finish runs to the two calls' entries
and the finish of the two outputs. -/
theorem expand_run_support {B : Type*} (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda))
    (variant : Grinding) (salt : Bits lambda) (address : Nat) (seed : Bits lambda) (g : Bits lambda × Bits lambda → B)
    (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda)) (table : List Bool → Option (Out lambda s wit rnd))
    (hashes : List (List Bool × Out lambda s wit rnd)) (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
    (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
    (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
      (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) B))
    (hout : out ∈ (runFixed procedure family 2
      (Spec.HashCipherProgram.bind (expandCall (s := s) (wit := wit) (rnd := rnd) layout variant salt address seed) fun children =>
        Program.done (g children)) table hashes ciphers log).support) :
    out = ⟨.done (g (layout.output (family (layout.key seed) (layout.input (cipherInput variant salt address false))),
        layout.output (family (layout.key seed) (layout.input (cipherInput variant salt address true))))), table, hashes,
      Spec.IdealCipher.entry (.encrypt (layout.key seed) (layout.input (cipherInput variant salt address true)))
          (family (layout.key seed) (layout.input (cipherInput variant salt address true))) ::
        Spec.IdealCipher.entry (.encrypt (layout.key seed) (layout.input (cipherInput variant salt address false)))
          (family (layout.key seed) (layout.input (cipherInput variant salt address false))) :: ciphers, false, log⟩ := by
  simp only [expandCall, Spec.HashCipherProgram.bind, runFixed, step_cipher, PMF.pure_bind,
    PMF.mem_support_pure_iff] at hout
  exact hout

/-- The inputs recorded by the tree expansion: the layout's inputs of cipher
inputs at addresses within the expanded range. -/
def TreeInput (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt : Bits lambda) (steps : Nat) (x : Bits lambda) : Prop :=
  ∃ i : Nat, ∃ b : Bool, 1 ≤ i ∧ i ≤ steps ∧ x = layout.input (cipherInput variant salt i b)

/-- The tree expansion records only inputs within its range, over the
starting history. -/
theorem tree_entries (layout : Spec.BAVCCipherProgram.Layout lambda (Bits lambda) (Bits lambda)) (variant : Grinding)
    (salt root : Bits lambda) (initial : Nat → Seed lambda) (family : Spec.IdealCipher.Family (Bits lambda) (Bits lambda))
    (steps : Nat) :
    ∀ (table : List Bool → Option (Out lambda s wit rnd)) (hashes : List (List Bool × Out lambda s wit rnd))
      (ciphers : List (Spec.IdealCipher.Entry (Bits lambda) (Bits lambda)))
      (log : List (Spec.RandomOracleTrace.Entry (List Bool) (Out lambda s wit rnd)))
      (out : Result (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda)
        (Program (List Bool) (Out lambda s wit rnd) (Bits lambda) (Bits lambda) (Nat → Seed lambda))),
      out ∈ (runFixed procedure family (2 * steps) (treeThrough (s := s) (wit := wit) (rnd := rnd) layout variant salt root initial steps)
        table hashes ciphers log).support →
      ∃ new, out.cipherHistory = new ++ ciphers ∧ ∀ e ∈ new, TreeInput layout variant salt steps e.input := by
  induction steps with
  | zero =>
    intro table hashes ciphers log out hout
    simp only [runFixed, PMF.mem_support_pure_iff] at hout
    subst hout
    exact ⟨[], rfl, fun e he => absurd he (List.not_mem_nil)⟩
  | succ k ih =>
    intro table hashes ciphers log out hout
    rw [runFixed_tree_succ] at hout
    obtain ⟨mid, hmid, hcont⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    obtain ⟨new₁, hnew₁, hform₁⟩ := ih table hashes ciphers log mid hmid
    obtain ⟨tree, htree⟩ := runFixed_bounded_done family _ _
      (SharedSigner.treeThrough_bounded layout variant salt root initial k) _ _ _ _ mid hmid
    unfold continueRun at hcont
    rw [htree] at hcont
    obtain ⟨inner, hinner, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hcont
    have hrun := expand_run_support layout variant salt (k + 1) (tree (k + 1)) _ family _ _ _ _ inner hinner
    subst heq
    subst hrun
    refine ⟨Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
          (layout.input (cipherInput variant salt (k + 1) true)))
          (family (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) true))) ::
        Spec.IdealCipher.entry (.encrypt (layout.key (tree (k + 1)))
          (layout.input (cipherInput variant salt (k + 1) false)))
          (family (layout.key (tree (k + 1))) (layout.input (cipherInput variant salt (k + 1) false))) :: new₁,
      ?_, fun e he => ?_⟩
    · show _ :: _ :: mid.cipherHistory = _
      rw [hnew₁, List.cons_append, List.cons_append]
    simp only [List.mem_cons] at he
    rcases he with rfl | rfl | he
    · exact ⟨k + 1, true, by omega, le_rfl, rfl⟩
    · exact ⟨k + 1, false, by omega, le_rfl, rfl⟩
    · obtain ⟨i, b, hi, hik, hx⟩ := hform₁ e he
      exact ⟨i, b, hi, by omega, hx⟩

end
end SDitH.Proofs.TreeRunEntries
