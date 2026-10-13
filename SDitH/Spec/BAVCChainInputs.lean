import SDitH.Spec.OracleChain
import SDitH.Spec.BLCHashChain
import SDitH.Spec.BAVCReconstructionProgram

/-! The concrete hash inputs of the verifier's chain, viewed as strings of
one product-valued oracle: row strings (domain byte 1, N commitments),
the outer string (domain byte 1, salt and tau row digests), the auxiliary
string (domain byte 2, root and corrections) and the mask input, which is
the auxiliary digest itself. The mention parser reads fixed-offset digest
windows: offset 0 (mask input), offset 8 (root inside the auxiliary string)
and the row-digest offsets of the outer string. These are explicit layout
definitions; their correspondence with the source byte strings is recorded
by the rfl lemmas relating them to the existing reconstruction inputs. -/

namespace SDitH.Spec.BAVCChainInputs

open BAVC DomainSeparation

variable {lambda tau N : Nat}

def rowString (row : Fin N → Digest lambda) : List Bool :=
  byteBits 1 ++ serializeArray row

def outerString (salt : Seed lambda) (rowHashes : Fin tau → Digest lambda) : List Bool :=
  byteBits 1 ++ (List.ofFn salt ++ serializeArray rowHashes)

def auxString (root : Digest lambda) (tail : List Bool) : List Bool :=
  BLCHashChain.auxQuery root tail

def maskInput (auxiliary : Digest lambda) : List Bool :=
  List.ofFn auxiliary

/-- The 2*lambda-bit window at an offset, zero-extended past the end. -/
def window (s : List Bool) (offset : Nat) : Digest lambda :=
  fun i => s.getD (offset + i.val) false

def rowOffset (lambda : Nat) (e : Nat) : Nat := 8 + lambda + 2 * lambda * e

def offsets (lambda tau : Nat) : Finset Nat :=
  {0, 8} ∪ (Finset.range tau).image (rowOffset lambda)

/-- Digest windows at the chain's fixed offsets. -/
def mentions (lambda tau : Nat) (s : List Bool) : Finset (Digest lambda) :=
  (offsets lambda tau).image (window s)

/-- The sink-first chain for one execution: auxiliary, outer, row. -/
def chain (salt : Seed lambda) (rows : Fin tau → Fin N → Digest lambda) (rowHashes : Fin tau → Digest lambda)
    (root : Digest lambda) (tail : List Bool) (auxiliary : Digest lambda) (e : Fin tau) : List (List Bool × Digest lambda) :=
  [(auxString root tail, auxiliary), (outerString salt rowHashes, root), (rowString (rows e), rowHashes e)]

end SDitH.Spec.BAVCChainInputs
