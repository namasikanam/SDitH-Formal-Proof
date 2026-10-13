import SDitH.Spec.Syndrome
import SDitH.Spec.RegularSupport
import Mathlib.Algebra.BigOperators.Fin

/-! The algorithm A_sd displayed in §5.1, printed p. 42.
The convention is that sigma moves old coordinate j to new coordinate sigma j;
columns and vectors are therefore pulled back along sigma.symm. The final
inverse permutation uses sigma. The solver is an explicit input. Its outputs
are not automatically assumed to solve the truncated RSD instance.
No runtime, distributional reduction, or heuristic uniqueness bound is asserted.
-/

namespace SDitH.Spec.SDReduction

noncomputable section
open scoped Classical

def vectorSupport {A F : Type*} [Fintype A] [Zero F] (x : A → F) : Finset A :=
  Finset.univ.filter (fun j => x j ≠ 0)

def permuteVector {A F : Type*} (sigma : Equiv.Perm A) (x : A → F) : A → F :=
  fun j => x (sigma.symm j)

def permuteInstance {F : Type*} {n k : Nat} (sigma : Equiv.Perm (Fin n))
    (inst : SDInstance F n k) : SDInstance F n k :=
  ⟨fun i j => inst.H i (sigma.symm j), inst.y⟩

/-- Keep the first n-k_rsd rows. Under the source condition k_rsd <= n,
this removes k_rsd-k_sd last rows. -/
def truncate {F : Type*} {n ksd krsd : Nat} (hkk : ksd ≤ krsd)
    (inst : SDInstance F n ksd) : SDInstance F n krsd :=
  ⟨fun i => inst.H (Fin.castLE (Nat.sub_le_sub_left hkk n) i),
    fun i => inst.y (Fin.castLE (Nat.sub_le_sub_left hkk n) i)⟩

def regularFlat {F : Type*} [Field F] {w m : Nat} (x : Fin (w * m) → F) : Prop :=
  Spec.Regular (fun i j => x (finProdFinEquiv (i, j)))

def RSDSolution {F : Type*} [Field F] {w m k : Nat}
    (inst : SDInstance F (w * m) k) (x : Fin (w * m) → F) : Prop :=
  inst.H.mulVec x = inst.y ∧ regularFlat x

/-- Steps 4–7. The source checks the full syndrome, but performs no additional
weight or regularity check on the solver's result. -/
def finish {F : Type*} [Field F] {n k : Nat} (inst : SDInstance F n k)
    (sigma : Equiv.Perm (Fin n)) (candidate : Option (Fin n → F)) :
    Option (Fin n → F) :=
  match candidate with
  | none => none
  | some xhat =>
    if (permuteInstance sigma inst).H.mulVec xhat = inst.y then
      some (permuteVector sigma.symm xhat)
    else none

/-- One invocation of the displayed reduction, including uniform permutation
and the supplied randomized RSD solver. -/
def run {F : Type*} [Field F] {n ksd krsd : Nat} (hkk : ksd ≤ krsd)
    (inst : SDInstance F n ksd)
    (solver : SDInstance F n krsd → PMF (Option (Fin n → F))) :
    PMF (Option (Fin n → F)) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin n))).bind fun sigma =>
    (solver (truncate hkk (permuteInstance sigma inst))).map (finish inst sigma)

end
end SDitH.Spec.SDReduction
