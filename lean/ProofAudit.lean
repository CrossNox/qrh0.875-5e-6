import Mathlib.Util.AssertNoSorry

open Lean Elab Command

/-- Reject declarations that depend on axioms outside the permitted set. -/
elab "#assert_standard_axioms " declaration:ident : command => do
  let declarationName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declaration
  let axioms ← collectAxioms declarationName
  let permittedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpectedAxioms := axioms.filter fun axiomName => !permittedAxioms.contains axiomName
  unless unexpectedAxioms.isEmpty do
    throwErrorAt declaration "{declarationName} depends on unexpected axioms: {unexpectedAxioms}"
  logInfo m!"'{declarationName}' depends on axioms: {axioms}"
