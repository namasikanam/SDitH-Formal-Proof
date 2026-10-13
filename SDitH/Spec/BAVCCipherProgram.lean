import SDitH.Spec.SeedVerification
import SDitH.Spec.BAVCBinding

/-! Cipher-query programs for the actual expansion and leaf/row stages of
Algorithm 9. Prefill, the distinct tree/nodes bindings and every error are
retained. The final row/outer hashes are a separate subsequent computation.
The layout consists only of conversions, with concrete full/III instances;
it contains no correctness, binding or security premise. -/

namespace SDitH.Spec.BAVCCipherProgram

open BAVC DomainSeparation OracleProgram

structure Layout (lambda : Nat) (Key Block : Type*) where
  key : Bits lambda → Key
  input : Bits lambda → Block
  output : Block → Bits lambda

def fullLayout (lambda : Nat) : Layout lambda (Bits lambda) (Bits lambda) := ⟨id, id, id⟩

def truncatedLayout : Layout 192 (Bits 256) (Bits 256) :=
  ⟨SeedPrimitives.pad192, SeedPrimitives.pad192, IdealCipherSeed.project192⟩

variable {lambda tau N : Nat} {Key Block A B : Type*}

def encStar (layout : Layout lambda Key Block) (family : IdealCipher.Family Key Block)
    (key input : Bits lambda) : Bits lambda :=
  layout.output (family (layout.key key) (layout.input input))

abbrev CipherProgram (Key Block A : Type*) := Program (IdealCipher.Query Key Block) Block A

def bindExcept (program : CipherProgram Key Block (Except ReconstructionError A))
    (next : A → CipherProgram Key Block (Except ReconstructionError B)) :
    CipherProgram Key Block (Except ReconstructionError B) :=
  OracleProgram.bind program fun result =>
    match result with
    | .error cause => .done (.error cause)
    | .ok value => next value

def expandProgram (layout : Layout lambda Key Block) (variant : Grinding)
    (salt : Seed lambda) (address : Nat) (seed : Seed lambda) : CipherProgram Key Block (Seed lambda × Seed lambda) :=
  SeedVerification.commitProgram layout.output (layout.key seed)
    (layout.input (SeedPrimitives.cipherInput variant salt address false))
    (layout.input (SeedPrimitives.cipherInput variant salt address true))

def commitProgram (layout : Layout lambda Key Block) (leafCount : Nat) (variant : Grinding)
    (salt seed : Seed lambda) (index : Nat) : CipherProgram Key Block (Digest lambda) :=
  OracleProgram.map (fun pair => SeedPrimitives.concatenate pair.1 pair.2)
    (expandProgram layout variant salt (leafCount + index) seed)

def expandStep (layout : Layout lambda Key Block) (variant : Grinding) (salt : Seed lambda)
    (tree : PartialTree lambda tau N) (nodes : NodesBinding lambda tau N) (i : Fin (tau * N - 1)) :
    CipherProgram Key Block (Except ReconstructionError (NodesBinding lambda tau N)) :=
  match tree (internalNode i) with
  | none => .done (.ok nodes)
  | some _ =>
    match nodes with
    | none => .done (.error .undefinedNodesArray)
    | some values =>
      match values (internalNode i) with
      | none => .done (.error .undefinedNodeRead)
      | some seed =>
        OracleProgram.map (fun children => .ok (some
          (Function.update (Function.update values (internalLeft i) (some children.1))
            (internalRight i) (some children.2)))) (expandProgram layout variant salt (i.val + 1) seed)

def expandThrough (layout : Layout lambda Key Block) (variant : Grinding) (salt : Seed lambda)
    (tree : PartialTree lambda tau N) (initial : NodesBinding lambda tau N) :
    (count : Nat) → count ≤ tau * N - 1 → CipherProgram Key Block (Except ReconstructionError (NodesBinding lambda tau N))
  | 0, _ => .done (.ok initial)
  | count + 1, hc => bindExcept (expandThrough layout variant salt tree initial count (by omega))
      (fun nodes => expandStep layout variant salt tree nodes ⟨count, by omega⟩)

def leafProgram (layout : Layout lambda Key Block) (variant : Grinding) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau)
    (nodes : NodesBinding lambda tau N) (e : Fin tau) (i : Fin N) :
    CipherProgram Key Block (Except ReconstructionError (ReconstructedLeaf lambda)) :=
  if i = hidden e then .done (.ok ⟨none, opening.hiddenCommitments e⟩)
  else match readNode nodes (leafNode e i) with
    | .error cause => .done (.error cause)
    | .ok seed => OracleProgram.map (fun commitment => .ok ⟨some seed, commitment⟩)
        (commitProgram layout (tau * N) variant salt seed (SeedTree.leafOffset e i))

def rowThrough (layout : Layout lambda Key Block) (variant : Grinding) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N) (e : Fin tau) :
    (count : Nat) → count ≤ N → CipherProgram Key Block (Except ReconstructionError (Vector (ReconstructedLeaf lambda) count))
  | 0, _ => .done (.ok #v[])
  | count + 1, hc => bindExcept (rowThrough layout variant salt hidden opening nodes e count (by omega)) fun row =>
      bindExcept (leafProgram layout variant salt hidden opening nodes e ⟨count, by omega⟩)
        (fun value => .done (.ok (row.push value)))

def rowsThrough (layout : Layout lambda Key Block) (variant : Grinding) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N) :
    (count : Nat) → count ≤ tau → CipherProgram Key Block (Except ReconstructionError (Vector (Vector (ReconstructedLeaf lambda) N) count))
  | 0, _ => .done (.ok #v[])
  | count + 1, hc => bindExcept (rowsThrough layout variant salt hidden opening nodes count (by omega)) fun rows =>
      bindExcept (rowThrough layout variant salt hidden opening nodes ⟨count, by omega⟩ N le_rfl)
        (fun row => .done (.ok (rows.push row)))

def reconstructionProgram (layout : Layout lambda Key Block) (variant : Grinding) (salt : Seed lambda)
    (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat) (initial : NodesBinding lambda tau N) :
    CipherProgram Key Block (Except ReconstructionError (Vector (Vector (ReconstructedLeaf lambda) N) tau)) :=
  match prefill hidden opening Topen with
  | .error cause => .done (.error cause)
  | .ok tree => bindExcept (expandThrough layout variant salt tree initial (tau * N - 1) le_rfl)
      (fun nodes => rowsThrough layout variant salt hidden opening nodes tau le_rfl)

def reconstructionBudget (tau N : Nat) : Nat := 2 * (tau * N - 1) + 2 * N * tau

end SDitH.Spec.BAVCCipherProgram
