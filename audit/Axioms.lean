import SDitH
import Lean.Util.CollectAxioms

/-! Audit every declaration under the project namespace, including internal
helpers. The allowlist contains only Lean's usual mathematical foundations.
Neither this audit nor a source scan proves correspondence to the PDF. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut visited : CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    if (`SDitH).isPrefixOf name || name.toString.startsWith "_private.SDitH" then
      count := count + 1
      let (_, next) := ((CollectAxioms.collect name).run env).run visited
      visited := next
      for ax in visited.axioms do
        unless allowed.contains ax do
          throwError "Forbidden axiom {ax} used by {name}"
  logInfo m!"Audited {count} SDitH declarations; all transitive axioms are allowlisted."

#print axioms SDitH.Final.literal_piop_not_complete
#print axioms SDitH.Final.table3_dimension_mismatch
#print axioms SDitH.Final.commitment_discrepancies
