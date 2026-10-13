import SDitH.Spec.BAVCCipherProgram
import SDitH.Spec.HashCipherEvaluation
import SDitH.Spec.BAVCBindingROM

/-! Algorithm 9 in source order: prefill, internal expansion, each row's leaf
calls followed immediately by its hash, then the salt-bound outer hash. Error
values and the distinct tree/nodes bindings are retained throughout. -/

namespace SDitH.Spec.BAVCReconstructionProgram

open BAVC HashCipherProgram

abbrev ReconstructionProgram (lambda : Nat) (Key Block A : Type*) :=
  Program (List Bool) (Digest lambda) Key Block A

structure Rows (lambda N count : Nat) where
  leaves : Vector (Vector (ReconstructedLeaf lambda) N) count
  hashes : Vector (Digest lambda) count

variable {lambda tau N : Nat} {Key Block A B : Type*}

def bindExcept (program : ReconstructionProgram lambda Key Block (Except ReconstructionError A))
    (next : A → ReconstructionProgram lambda Key Block (Except ReconstructionError B)) :
    ReconstructionProgram lambda Key Block (Except ReconstructionError B) :=
  HashCipherProgram.bind program fun result =>
    match result with
    | .error cause => .done (.error cause)
    | .ok value => next value

def rowInput (row : Vector (ReconstructedLeaf lambda) N) : List Bool :=
  byteBits 1 ++ serializeArray (fun i : Fin N => row[i].commitment)

def rowsThrough (layout : BAVCCipherProgram.Layout lambda Key Block) (variant : DomainSeparation.Grinding)
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (nodes : NodesBinding lambda tau N) :
    (count : Nat) → count ≤ tau → ReconstructionProgram lambda Key Block (Except ReconstructionError (Rows lambda N count))
  | 0, _ => .done (.ok ⟨#v[], #v[]⟩)
  | count + 1, hc => bindExcept (rowsThrough layout variant salt hidden opening nodes count (by omega)) fun rows =>
      bindExcept (liftCipher (BAVCCipherProgram.rowThrough layout variant salt hidden opening nodes ⟨count, by omega⟩ N le_rfl)) fun row =>
        .hash (rowInput row) fun digest => .done (.ok ⟨rows.leaves.push row, rows.hashes.push digest⟩)

def outerInput (salt : Seed lambda) (rows : Rows lambda N tau) : List Bool :=
  byteBits 1 ++ (List.ofFn salt ++ serializeArray (fun e : Fin tau => rows.hashes[e]))

def finish (salt : Seed lambda) (rows : Rows lambda N tau) :
    ReconstructionProgram lambda Key Block (Except ReconstructionError (Reconstructed lambda tau N)) :=
  .hash (outerInput salt rows) fun root => .done (.ok ⟨root, fun e i => rows.leaves[e][i].seed⟩)

def reconstruct (layout : BAVCCipherProgram.Layout lambda Key Block) (variant : DomainSeparation.Grinding)
    (salt : Seed lambda) (hidden : Fin tau → Fin N) (opening : Opening lambda tau) (Topen : Nat)
    (initial : NodesBinding lambda tau N) : ReconstructionProgram lambda Key Block (Except ReconstructionError (Reconstructed lambda tau N)) :=
  match prefill hidden opening Topen with
  | .error cause => .done (.error cause)
  | .ok tree => bindExcept (liftCipher (BAVCCipherProgram.expandThrough layout variant salt tree initial (tau * N - 1) le_rfl)) fun nodes =>
      bindExcept (rowsThrough layout variant salt hidden opening nodes tau le_rfl) (finish salt)

def budget (tau N : Nat) : Nat := 2 * (tau * N - 1) + (2 * N + 1) * tau + 1

/-- This totalized hash is used only to state value correspondence. Successful
execution proves every required row/outer lookup is present. -/
def primitives (layout : BAVCCipherProgram.Layout lambda Key Block) (variant : DomainSeparation.Grinding)
    (family : IdealCipher.Family Key Block) (table : List Bool → Option (Digest lambda)) : Primitives lambda :=
  SeedPrimitives.bavcPrimitives (tau * N) variant (BAVCCipherProgram.encStar layout family)
    (fun input => (table input).getD (fun _ => false))

def RowsCovered (table : List Bool → Option (Digest lambda)) {count : Nat} (rows : Rows lambda N count) : Prop :=
  ∀ e : Fin count, table (rowInput rows.leaves[e]) = some rows.hashes[e]

end SDitH.Spec.BAVCReconstructionProgram
