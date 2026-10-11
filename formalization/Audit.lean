import CircularLaw
import Lean.Util.CollectAxioms

example : CircularLaw.MainTheorem := CircularLaw.main_circular_law_theorem

/-!
Audit the axiom dependencies of every public project declaration.
Only the standard foundations used by Lean/mathlib are allowed. In particular,
an admitted proof or a new project axiom fails this check.

Run with `lake env lean Audit.lean` after `lake build`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let projectNamespace := Name.mkSimple "CircularLaw"
  let mut declarations := 0
  let mut theorems := 0
  -- Share the traversal state across declarations. Every dependency is
  -- still visited, but common mathlib proof trees are traversed only once.
  let mut auditState : CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    if projectNamespace.isPrefixOf name then
      declarations := declarations + 1
      if let .thmInfo _ := info then
        if name.getPrefix == projectNamespace then
          theorems := theorems + 1
      let (_, nextState) := ((CollectAxioms.collect name).run env).run auditState
      auditState := nextState
      for dependency in auditState.axioms do
        unless allowed.contains dependency do
          throwError "{name} depends on disallowed axiom {dependency}"
  logInfo m!"Axiom audit passed: {declarations} declarations including generated helpers; {theorems} named theorems."
  logInfo "MainTheorem is proved by CircularLaw.main_circular_law_theorem."
