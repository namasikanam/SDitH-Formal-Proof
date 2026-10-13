import SDitH.Spec.SDReduction

/-! Probability experiment for the actual §5.1 reduction, printed pp. 42–43.
The input distribution is explicit. No distributional correspondence, solver
success parameter or uniqueness estimate is assumed by these definitions. -/

namespace SDitH.Spec.SDReductionGame

open SDReduction
noncomputable section
open scoped Classical ENNReal

structure Outcome (F : Type*) (n ksd : Nat) where
  input : SDInstance F n ksd
  permutation : Equiv.Perm (Fin n)
  candidate : Option (Fin n → F)

def experiment {F : Type*} [Field F] {n ksd krsd : Nat} (hkk : ksd ≤ krsd)
    (inputs : PMF (SDInstance F n ksd))
    (solver : SDInstance F n krsd → PMF (Option (Fin n → F))) :
    PMF (Outcome F n ksd) :=
  inputs.bind fun inst =>
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).bind fun sigma =>
      (solver (truncate hkk (permuteInstance sigma inst))).map fun candidate =>
        ⟨inst, sigma, candidate⟩

def output {F : Type*} [Field F] {n ksd : Nat} (o : Outcome F n ksd) :
    Option (Fin n → F) := finish o.input o.permutation o.candidate

def Returned {F : Type*} {n ksd : Nat} (o : Outcome F n ksd) : Prop :=
  o.candidate.isSome

def Succeeded {F : Type*} [Field F] {n ksd : Nat} (o : Outcome F n ksd) : Prop :=
  (output o).isSome

def FullRegular {F : Type*} [Field F] {w m ksd : Nat}
    (o : Outcome F (w * m) ksd) : Prop :=
  ∃ z, RSDSolution (permuteInstance o.permutation o.input) z

def UniqueTruncated {F : Type*} [Field F] {w m ksd krsd : Nat}
    (hkk : ksd ≤ krsd) (o : Outcome F (w * m) ksd) : Prop :=
  ∀ a b,
    RSDSolution (truncate hkk (permuteInstance o.permutation o.input)) a →
    RSDSolution (truncate hkk (permuteInstance o.permutation o.input)) b → a = b

def eventMass {A : Type*} (p : PMF A) (event : A → Prop) : ℝ≥0∞ :=
  p.toOuterMeasure {a | event a}

/-- Conditional probability represented by its exact event-mass ratio. Any use
of cancellation must establish that the conditioning event has positive mass. -/
def conditionalMass {A : Type*} (p : PMF A) (event given : A → Prop) : ℝ≥0∞ :=
  eventMass p (fun a => given a ∧ event a) / eventMass p given

end
end SDitH.Spec.SDReductionGame
