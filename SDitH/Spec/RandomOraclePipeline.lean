import SDitH.Spec.RandomOracleCollision

namespace SDitH.Spec.RandomOraclePipeline

open RandomOracleCollision
noncomputable section

/-- Run an adversarial phase and then an answer-dependent verification phase
against the same table. The second phase receives the adversary's public state,
not its private table/log. Both phases' query collisions are retained. -/
def experiment {Input Output A B : Type*} [Fintype Output] [Nonempty Output]
    (first : Procedure Input Output A) (q : Nat) (initial : A)
    (second : Procedure Input Output B) (k : Nat) (next : A → B) : PMF (Result Input Output B) :=
  (RandomOracleCollision.experiment first q initial).bind fun start =>
    (run second k (next start.state) start.table start.history).map fun out =>
      { out with collided := start.collided || out.collided }

end
end SDitH.Spec.RandomOraclePipeline
