import SDitH.Spec.Syndrome
import SDitH.Spec.Parameters
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn

/-! Algorithm 1 after position sampling, printed p. 11.

`width j = mu_j - 1`, so every radix is positive by construction. Successive
division starts with j=0, exactly as in line 9; its first digit is therefore the
least significant mixed-radix digit. The position sampler/PRG remains outside
this deterministic computation. No Table-3 tensor dimension equality is imposed.
-/

namespace SDitH.Spec.WitnessExpansion

open scoped BigOperators

def radixSize : {d : Nat} → (Fin d → Nat) → Nat
  | 0, _ => 1
  | _ + 1, width => (width 0 + 1) * radixSize (fun j => width j.succ)

/-- Stored widths from a submitted parameter row. The source's positive arities
are checked separately; subtraction does not validate arbitrary parameter data. -/
def parameterWidths (p : RSDParameters) : Fin p.arities.length → Nat :=
  fun j => p.arities.get j - 1

structure PositionExpansion {d : Nat} (width : Fin d → Nat) where
  digits : (j : Fin d) → Fin (width j + 1)
  remaining : Nat

/-- Line 9's actual successive state updates. The final quotient is retained,
so out-of-range positions are not silently identified with their truncated code. -/
def splitPosition : {d : Nat} → (width : Fin d → Nat) → Nat → PositionExpansion width
  | 0, _, position => ⟨fun j => Fin.elim0 j, position⟩
  | _ + 1, width, position =>
    let tail := splitPosition (fun j => width j.succ) (position / (width 0 + 1))
    { digits := Fin.cases ⟨position % (width 0 + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
        tail.digits
      remaining := tail.remaining }

/-- The flattening inverse dictated by line 9. This names the coordinate order
explicitly; it does not assert an unstated convention for a tensor library. -/
def joinDigits : {d : Nat} → (width : Fin d → Nat) → ((j : Fin d) → Fin (width j + 1)) → Nat
  | 0, _, _ => 0
  | _ + 1, width, digits =>
    (digits 0).val + (width 0 + 1) * joinDigits (fun j => width j.succ) (fun j => digits j.succ)

variable {F : Type*} [Field F]

/-- The increasing-j loop, including append of precisely mu_j-1 coordinates.
It implements lines 8–11 directly rather than assuming a tensor encoding. -/
noncomputable def witnessLoop : {d : Nat} → (width : Fin d → Nat) → Nat → List F
  | 0, _, _ => []
  | _ + 1, width, position =>
    List.ofFn (fun k : Fin (width 0) =>
      if k.val = position % (width 0 + 1) then (1 : F) else 0) ++
      witnessLoop (fun j => width j.succ) (position / (width 0 + 1))

/-- Structured view of the stored selector coordinates; the equality of this
view with the literal append loop is a theorem in the proof module. -/
noncomputable def selector {d : Nat} (width : Fin d → Nat) (position : Nat)
    (j : Fin d) : Fin (width j) → F :=
  fun k => elementary ((splitPosition width position).digits j) k.castSucc

structure Expanded (F : Type*) (w m : Nat) where
  solution : Fin (w * m) → F
  witness : List F

/-- Lines 3–12. The original sampled positions produce x before the quotient
loop mutates its local copies; x is not formed from the final quotient values.
The flat solution has w*m coordinates, leaving n=w*m as a separate obligation. -/
noncomputable def expandAfterSampling {w m d : Nat} (width : Fin d → Nat)
    (positions : Fin w → Fin m) : Expanded F w m :=
  { solution := fun a =>
      elementary (positions (finProdFinEquiv.symm a).1) (finProdFinEquiv.symm a).2
    witness := (List.ofFn (fun i => witnessLoop width (positions i).val)).flatten }

end SDitH.Spec.WitnessExpansion
