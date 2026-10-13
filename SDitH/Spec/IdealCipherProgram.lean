import SDitH.Spec.IdealCipher
import SDitH.Spec.OracleProgram

/-! Execute finite query programs against one ideal-cipher family. All answers,
including inverse and repeated requests, come from that family. The graph logs
every call; completing a program never requires a prior-query guard. -/

namespace SDitH.Spec.IdealCipherProgram

open IdealCipher OracleProgram

variable {Key Block A : Type*}

def execute (family : Family Key Block) :
    Program (Query Key Block) Block A → List (Entry Key Block) → A × List (Entry Key Block)
  | .done value, history => (value, history)
  | .query request next, history =>
      execute family (next (answer family request)) (entry request (answer family request) :: history)

noncomputable def procedure : IdealCipher.Procedure Key Block (Program (Query Key Block) Block A) where
  step program := PMF.pure (match program with
    | .done _ => .stop
    | .query request next => .query request next)

end SDitH.Spec.IdealCipherProgram
