import Lean.Elab.Tactic.VCGen.Frontend
import Ascent.Tactic.VCGen.Driver

/-!
# The `ascend'` tactic

`ascend'` runs the forked worklist on a goal `⦃P⦄ c ⪯[γ] a ⦃Q; E⦄`. The `wrp` goals use the
`@[wrp_spec]` database, and the `wp` goals use the `@[spec]` database. A natural metavariable in
`a` is a synthesis hole.
-/

open Lean Meta Elab Tactic Sym

namespace Lean.Elab.Tactic.VCGen.Ascend

open Lean.Elab.Tactic.VCGen.SpecAttr

syntax (name := ascendTac) "ascend'" : tactic

/-- Unseal the abstract program hole of a `Refinement` goal, so that rule application can assign
it. -/
def unsealAbstractHole (goal : MVarId) : MetaM Unit := do
  let target ← goal.getType
  unless target.isAppOfArity ``Ascent.Refinement 22 do return
  let .mvar mvarId := target.getAppArgs[14]!.getAppFn | return
  if (← mvarId.getDecl).kind matches .syntheticOpaque then
    mvarId.setKind .natural

@[tactic ascendTac]
def elabAscend : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  unsealAbstractHole goal
  let ctx : Context := { backwardRules := ← mkBackwardRules, internalize := false }
  let scope : Scope := { specs := ← getWrpSpecTheorems }
  let coreScope : Scope := { specs := ← getSpecTheorems }
  let params ← Grind.mkDefaultParams { clean := false }
  let (_, state) ← Grind.GrindTacticM.runAtGoal goal params (sym := true) do
    let g ← Lean.Elab.Tactic.Grind.getMainGoal
    let result ← Lean.Elab.Tactic.Grind.liftGrindM (run g ctx scope coreScope)
    Lean.Elab.Tactic.Grind.replaceMainGoal result.vcs.toList
  replaceMainGoal (state.goals.map (·.mvarId))

end Lean.Elab.Tactic.VCGen.Ascend
