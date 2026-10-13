import SDitH.Spec.RandomOracleCollision

/-! Finite adaptive oracle programs used to execute the source hash calls.
This syntax contains only return and query; probabilities come from the same
shared lazy oracle as the adversarial procedure. Bounded is a property to prove
about a program, not a field asserting its correctness or security. -/

namespace SDitH.Spec.OracleProgram

inductive Program (Input Output A : Type*) where
  | done (value : A)
  | query (input : Input) (next : Output → Program Input Output A)

variable {Input Output A B : Type*}

def bind (program : Program Input Output A) (next : A → Program Input Output B) : Program Input Output B :=
  match program with
  | .done value => next value
  | .query input tail => .query input (fun answer => bind (tail answer) next)

def map (f : A → B) (program : Program Input Output A) : Program Input Output B :=
  bind program (fun a => .done (f a))

def array : (n : Nat) → (Fin n → Input) → Program Input Output (Fin n → Output)
  | 0, _ => .done Fin.elim0
  | n + 1, inputs => .query (inputs 0) (fun answer =>
      map (Fin.cons answer) (array n (fun i => inputs i.succ)))

def Bounded : Nat → Program Input Output A → Prop
  | _, .done _ => True
  | 0, .query _ _ => False
  | n + 1, .query _ next => ∀ answer, Bounded n (next answer)

/-- A successful evaluation using only entries present in this one final
table. Operational execution must establish this relation. -/
inductive Evaluates (table : Input → Option Output) : Program Input Output A → A → Prop where
  | done (value : A) : Evaluates table (.done value) value
  | query (input : Input) (next : Output → Program Input Output A) (answer : Output) (value : A)
      (stored : table input = some answer) (tail : Evaluates table (next answer) value) :
      Evaluates table (.query input next) value

noncomputable def procedure : RandomOracleCollision.Procedure Input Output (Program Input Output A) where
  step program := PMF.pure (match program with
    | .done _ => .stop
    | .query input next => .query input next)

end SDitH.Spec.OracleProgram
