import Lean

/-!
# Enforcing transitive proof-dependency gate

Use after importing the modules to be checked. Declarations are selected both
by namespace and by their defining module, so private and out-of-namespace
helpers from an in-scope module are included. No theorem is proved here.
-/

open Lean Elab Command

namespace BongCI

/-- Reject any in-scope declaration with dependencies outside the fixed standard allowance. -/
def checkAxioms (roots : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let inScope := fun name ↦
    roots.any (·.isPrefixOf name) ||
      match env.getModuleIdxFor? name with
      | some index => roots.any (·.isPrefixOf env.header.moduleNames[index.toNat]!)
      | none => roots.any (·.isPrefixOf env.mainModule)
  let mut checked := 0
  for (name, _) in env.constants do
    if inScope name then
      checked := checked + 1
      let dependencies ← Lean.collectAxioms name
      let rejected := dependencies.filter fun dependency ↦ !allowed.contains dependency
      unless rejected.isEmpty do
        throwError ("AXIOM_GATE_REJECT " ++ toString name ++ ": " ++ toString rejected)
  if checked == 0 then
    throwError "AXIOM_GATE_EMPTY: no declarations selected"
  logInfo ("AXIOM_GATE_PASS: " ++ toString checked ++ " declarations checked")

end BongCI
