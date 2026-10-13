import Mathlib.Probability.Distributions.Uniform

/-! Lazy random-oracle semantics used by the explicit ROM security games.
This is a probability-model definition, not an assertion that SHAKE implements
a random function. Repeated queries return their stored value; only absent
queries sample independently. -/

namespace SDitH.Spec.RandomOracle

noncomputable def query {Input Output : Type*} [DecidableEq Input]
    [Fintype Output] [Nonempty Output]
    (table : Input → Option Output) (input : Input) :
    PMF (Output × (Input → Option Output)) :=
  match table input with
  | some answer => PMF.pure (answer, table)
  | none => (PMF.uniformOfFintype Output).map fun answer =>
      (answer, Function.update table input (some answer))

end SDitH.Spec.RandomOracle
