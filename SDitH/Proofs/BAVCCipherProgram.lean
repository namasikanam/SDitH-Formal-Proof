import SDitH.Spec.BAVCCipherProgram
import SDitH.Proofs.HashCipherProgram
import SDitH.Proofs.SeedVerification

namespace SDitH.Proofs.BAVCCipherProgram

open Spec.BAVC Spec.BAVCCipherProgram Spec.OracleProgram
open Spec.IdealCipher Spec.IdealCipherProgram

variable {lambda tau N : Nat} {Key Block A B : Type*}

theorem full_encStar (family : Family (Spec.DomainSeparation.Bits lambda) (Spec.DomainSeparation.Bits lambda)) :
    encStar (fullLayout lambda) family = (fun key input => family key input) := rfl

theorem truncated_encStar (family : Family (Spec.DomainSeparation.Bits 256) (Spec.DomainSeparation.Bits 256)) :
    encStar truncatedLayout family = Spec.SeedPrimitives.encStarIII (fun key input => family key input) := rfl

theorem execute_map_value (family : Family Key Block) (program : CipherProgram Key Block A)
    (f : A → B) (history : List (Entry Key Block)) :
    (execute family (Spec.OracleProgram.map f program) history).1 = f (execute family program history).1 := by
  rw [Spec.OracleProgram.map, IdealCipherProgram.execute_bind]
  rfl

theorem execute_bindExcept_value (family : Family Key Block)
    (program : CipherProgram Key Block (Except ReconstructionError A))
    (next : A → CipherProgram Key Block (Except ReconstructionError B))
    (value : Except ReconstructionError A) (f : A → Except ReconstructionError B)
    (hp : ∀ history, (execute family program history).1 = value)
    (hn : ∀ a history, (execute family (next a) history).1 = f a)
    (history : List (Entry Key Block)) :
    (execute family (bindExcept program next) history).1 = value.bind f := by
  rw [bindExcept, IdealCipherProgram.execute_bind, hp]
  cases value with
  | error cause => rfl
  | ok value => exact hn value _

theorem bounded_bindExcept (program : CipherProgram Key Block (Except ReconstructionError A))
    (next : A → CipherProgram Key Block (Except ReconstructionError B)) (q k : Nat)
    (hp : Bounded q program) (hn : ∀ a, Bounded k (next a)) :
    Bounded (q + k) (bindExcept program next) := by
  apply OracleProgram.bounded_bind _ _ q k hp
  intro value
  cases value with
  | error cause => cases k <;> trivial
  | ok value => exact hn value

theorem expand_value (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (salt : Seed lambda) (address : Nat) (seed : Seed lambda) (history : List (Entry Key Block)) :
    (execute family (expandProgram layout variant salt address seed) history).1 =
      Spec.SeedPrimitives.expandSeed variant (encStar layout family) salt address seed := rfl

theorem expand_bounded (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (address : Nat) (seed : Seed lambda) :
    Bounded 2 (expandProgram layout variant salt address seed) := by
  intro _ _
  trivial

theorem commit_value (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (leafCount : Nat) (salt seed : Seed lambda) (index : Nat) (history : List (Entry Key Block)) :
    (execute family (commitProgram layout leafCount variant salt seed index) history).1 =
      Spec.SeedPrimitives.commitSeed leafCount variant (encStar layout family) salt seed index := by
  rw [commitProgram, execute_map_value, expand_value]
  rfl

theorem commit_bounded (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (leafCount : Nat) (salt seed : Seed lambda) (index : Nat) :
    Bounded 2 (commitProgram layout leafCount variant salt seed index) :=
  OracleProgram.bounded_map _ _ 2 (expand_bounded layout variant salt (leafCount + index) seed)

theorem step_value (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (hash : List Bool → Digest lambda) (salt : Seed lambda)
    (tree : PartialTree lambda tau N) (nodes : NodesBinding lambda tau N) (i : Fin (tau * N - 1))
    (history : List (Entry Key Block)) :
    (execute family (expandStep layout variant salt tree nodes i) history).1 =
      expandPartialStep (Spec.SeedPrimitives.bavcPrimitives (tau * N) variant (encStar layout family) hash) salt tree nodes i := by
  unfold expandStep expandPartialStep
  cases tree (internalNode i) with
  | none => rfl
  | some seed =>
    cases nodes with
    | none => rfl
    | some values =>
      dsimp only
      cases values (internalNode i) with
      | none => rfl
      | some seed =>
        rw [execute_map_value, expand_value]
        rfl

theorem step_bounded (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (tree : PartialTree lambda tau N) (nodes : NodesBinding lambda tau N) (i : Fin (tau * N - 1)) :
    Bounded 2 (expandStep layout variant salt tree nodes i) := by
  unfold expandStep
  cases tree (internalNode i) with
  | none => trivial
  | some seed =>
    cases nodes with
    | none => trivial
    | some values =>
      dsimp only
      cases values (internalNode i) with
      | none => trivial
      | some seed => exact OracleProgram.bounded_map _ _ 2 (expand_bounded layout variant salt (i.val + 1) seed)

theorem expansion_value (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (hash : List Bool → Digest lambda) (salt : Seed lambda)
    (tree : PartialTree lambda tau N) (initial : NodesBinding lambda tau N)
    (count : Nat) (hc : count ≤ tau * N - 1) (history : List (Entry Key Block)) :
    (execute family (expandThrough layout variant salt tree initial count hc) history).1 =
      expandPartialThrough (Spec.SeedPrimitives.bavcPrimitives (tau * N) variant (encStar layout family) hash) salt tree initial count hc := by
  induction count generalizing history with
  | zero => rfl
  | succ count ih =>
    exact execute_bindExcept_value family _ _ _ _ (ih (by omega))
      (fun nodes history => step_value layout variant family hash salt tree nodes ⟨count, by omega⟩ history) history

theorem expansion_bounded (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (tree : PartialTree lambda tau N) (initial : NodesBinding lambda tau N)
    (count : Nat) (hc : count ≤ tau * N - 1) : Bounded (2 * count) (expandThrough layout variant salt tree initial count hc) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    simpa only [Nat.mul_add, Nat.mul_one] using
      bounded_bindExcept _ _ (2 * count) 2 (ih (by omega))
        (fun nodes => step_bounded layout variant salt tree nodes ⟨count, by omega⟩)

theorem leaf_value (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (hash : List Bool → Digest lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (e : Fin tau) (i : Fin N) (history : List (Entry Key Block)) :
    (execute family (leafProgram layout variant salt hidden opening nodes e i) history).1 =
      reconstructLeaf (Spec.SeedPrimitives.bavcPrimitives (tau * N) variant (encStar layout family) hash) salt hidden opening nodes e i := by
  unfold leafProgram reconstructLeaf
  split
  · rfl
  · cases readNode nodes (leafNode e i) with
    | error cause => rfl
    | ok seed =>
      rw [execute_map_value, commit_value]
      rfl

theorem leaf_bounded (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (e : Fin tau) (i : Fin N) : Bounded 2 (leafProgram layout variant salt hidden opening nodes e i) := by
  unfold leafProgram
  split
  · trivial
  · cases readNode nodes (leafNode e i) with
    | error cause => trivial
    | ok seed => exact OracleProgram.bounded_map _ _ 2 (commit_bounded layout variant (tau * N) salt seed (Spec.SeedTree.leafOffset e i))

theorem row_value (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (hash : List Bool → Digest lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N) (e : Fin tau)
    (count : Nat) (hc : count ≤ N) (history : List (Entry Key Block)) :
    (execute family (rowThrough layout variant salt hidden opening nodes e count hc) history).1 =
      reconstructRowThrough (Spec.SeedPrimitives.bavcPrimitives (tau * N) variant (encStar layout family) hash)
        salt hidden opening nodes e count hc := by
  induction count generalizing history with
  | zero => rfl
  | succ count ih =>
    apply execute_bindExcept_value family _ _ _ _ (ih (by omega))
    intro row history
    exact execute_bindExcept_value family _ _ _ _
      (leaf_value layout variant family hash salt hidden opening nodes e ⟨count, by omega⟩)
      (fun value _ => rfl) history

theorem row_bounded (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N) (e : Fin tau)
    (count : Nat) (hc : count ≤ N) : Bounded (2 * count) (rowThrough layout variant salt hidden opening nodes e count hc) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [Nat.mul_add, Nat.mul_one]
    apply bounded_bindExcept _ _ (2 * count) 2 (ih (by omega))
    intro row
    exact bounded_bindExcept _ _ 2 0 (leaf_bounded layout variant salt hidden opening nodes e ⟨count, by omega⟩)
      (fun _ => trivial)

theorem rows_value (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (hash : List Bool → Digest lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (count : Nat) (hc : count ≤ tau) (history : List (Entry Key Block)) :
    (execute family (rowsThrough layout variant salt hidden opening nodes count hc) history).1 =
      reconstructRowsThrough (Spec.SeedPrimitives.bavcPrimitives (tau * N) variant (encStar layout family) hash)
        salt hidden opening nodes count hc := by
  induction count generalizing history with
  | zero => rfl
  | succ count ih =>
    apply execute_bindExcept_value family _ _ _ _ (ih (by omega))
    intro rows history
    exact execute_bindExcept_value family _ _ _ _
      (row_value layout variant family hash salt hidden opening nodes ⟨count, by omega⟩ N le_rfl)
      (fun row _ => rfl) history

theorem rows_bounded (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N)
    (count : Nat) (hc : count ≤ tau) : Bounded (2 * N * count) (rowsThrough layout variant salt hidden opening nodes count hc) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [Nat.mul_add, Nat.mul_one]
    apply bounded_bindExcept _ _ (2 * N * count) (2 * N) (ih (by omega))
    intro rows
    exact bounded_bindExcept _ (fun row => .done (.ok (rows.push row))) (2 * N) 0
      (row_bounded layout variant salt hidden opening nodes ⟨count, by omega⟩ N le_rfl) (fun _ => trivial)

/-- Exact agreement with the existing source rows, including errors. This
does not identify the source's two separately named arrays or change its guards. -/
theorem reconstruction_value (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (hash : List Bool → Digest lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N)
    (history : List (Entry Key Block)) :
    (execute family (reconstructionProgram layout variant salt hidden opening Topen initial) history).1 =
      Spec.BAVCBinding.reconstructionRows (Spec.SeedPrimitives.bavcPrimitives (tau * N) variant (encStar layout family) hash)
        salt hidden opening Topen initial := by
  unfold reconstructionProgram Spec.BAVCBinding.reconstructionRows
  cases prefill hidden opening Topen with
  | error cause => rfl
  | ok tree =>
    exact execute_bindExcept_value family _ _ _ _
      (expansion_value layout variant family hash salt tree initial (tau * N - 1) le_rfl)
      (fun nodes => rows_value layout variant family hash salt hidden opening nodes tau le_rfl) history

theorem reconstruction_bounded (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N) :
    Bounded (reconstructionBudget tau N) (reconstructionProgram layout variant salt hidden opening Topen initial) := by
  unfold reconstructionProgram
  cases prefill hidden opening Topen with
  | error cause => cases reconstructionBudget tau N <;> trivial
  | ok tree =>
    exact bounded_bindExcept _ _ (2 * (tau * N - 1)) (2 * N * tau)
      (expansion_bounded layout variant salt tree initial (tau * N - 1) le_rfl)
      (fun nodes => rows_bounded layout variant salt hidden opening nodes tau le_rfl)

/-- The cipher stages run in the shared interpreter with exactly the source
result and actual query graph. Every error is returned as an error value;
completion does not mean that reconstruction succeeded. -/
theorem run_shared {Input Digest' : Type*} [Fintype Digest'] [Nonempty Digest']
    (layout : Layout lambda Key Block) (variant : Spec.DomainSeparation.Grinding)
    (family : Family Key Block) (hash : List Bool → Digest lambda) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N)
    (table : Input → Option Digest') (hashes : List (Input × Digest')) (ciphers : List (Entry Key Block)) :
    Spec.HashCipher.runFixed Spec.HashCipherProgram.procedure family (reconstructionBudget tau N)
      (Spec.HashCipherProgram.liftCipher (reconstructionProgram layout variant salt hidden opening Topen initial)) table hashes ciphers =
      PMF.pure ⟨.done (Spec.BAVCBinding.reconstructionRows
        (Spec.SeedPrimitives.bavcPrimitives (tau * N) variant (encStar layout family) hash) salt hidden opening Topen initial),
        table, hashes, (execute family (reconstructionProgram layout variant salt hidden opening Topen initial) ciphers).2, false⟩ := by
  rw [HashCipherProgram.run_liftCipher,
    IdealCipherProgram.runFixed_execute family _ _ (reconstruction_bounded layout variant salt hidden opening Topen initial),
    PMF.pure_map]
  simp only [Spec.HashCipherProgram.liftCipherResult, Spec.HashCipherProgram.liftCipher,
    reconstruction_value layout variant family hash]

end SDitH.Proofs.BAVCCipherProgram
