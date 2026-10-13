import SDitH.Spec.RandomOracleMention

/-! Two independent lazy oracles as the components of one product-valued
lazy oracle: the digest component answers hash queries and the matrix
component answers mask queries. Each query input is answered by one fresh
pair, of which the caller uses one component. This is an explicit model
choice for stating composed bounds; it asserts nothing about concrete
SHAKE or its XOF mode, whose correspondence is a separate obligation. -/

namespace SDitH.Spec.ProductOracle

open RandomOracleTrace RandomOracleTrap
open scoped Classical

variable {Input D M : Type*}

/-- Mask trap on the matrix component, for a vector-valued function of the
query input that may also depend on the table before the query. -/
noncomputable def tableMaskTrap {K : Type*} [CommRing K] {s payload : Nat}
    (vector : (Input → Option (D × Matrix (Fin s) (Fin payload) K)) → Input → Fin (s + payload) → K)
    (before : Input → Option (D × Matrix (Fin s) (Fin payload) K)) (input : Input)
    (answer : D × Matrix (Fin s) (Fin payload) K) : Bool :=
  kernelTrap (vector before) input answer.2

/-- A fresh digest component equal to a value mentioned by an earlier fresh
query input. -/
noncomputable def digestMention (mentions : Input → Finset D) (trace : List (Entry Input (D × M)))
    (_input : Input) (answer : D × M) : Bool :=
  trace.any fun entry => decide (answer.1 ∈ mentions entry.input)

end SDitH.Spec.ProductOracle
