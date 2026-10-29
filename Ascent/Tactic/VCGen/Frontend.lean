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
it. Returns the hole. -/
def unsealAbstractHole (goal : MVarId) : MetaM (Option MVarId) := do
  let target := (← instantiateMVars (← goal.getType)).headBeta
  unless target.isAppOfArity ``Ascent.Refinement 22 do return none
  let .mvar mvarId := target.getAppArgs[14]!.getAppFn | return none
  if (← mvarId.getDecl).kind matches .syntheticOpaque then
    mvarId.setKind .natural
  return some mvarId

/-- Restore the local context of the hole, and check that the synthesized program uses only the
free variables of that context. -/
def checkHoleScope (hole : MVarId) (decl : MetavarDecl) : MetaM Unit := do
  modifyMCtx (·.modifyExprMVarDecl hole fun d =>
    { d with lctx := decl.lctx, localInstances := decl.localInstances })
  let val ← instantiateMVars (mkMVar hole)
  if (val.find? fun e => e.isFVar && !decl.lctx.contains e.fvarId!).isSome then
    throwError "ascend: the synthesized abstract program mentions a variable that the run \
      introduced, such as the concrete state"

@[tactic ascendTac]
def elabAscend : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let hole? ← unsealAbstractHole goal
  let holeDecl? ← hole?.mapM (·.getDecl)
  let ctx : Context := { backwardRules := ← mkBackwardRules, internalize := false }
  let scope : Scope := { specs := ← getWrpSpecTheorems }
  let coreScope : Scope := { specs := ← getSpecTheorems }
  let params ← Grind.mkDefaultParams { clean := false }
  let (_, state) ← Grind.GrindTacticM.runAtGoal goal params (sym := true) do
    let g ← Lean.Elab.Tactic.Grind.getMainGoal
    let result ← Lean.Elab.Tactic.Grind.liftGrindM (run g ctx scope coreScope)
    Lean.Elab.Tactic.Grind.replaceMainGoal result.vcs.toList
  if let (some hole, some decl) := (hole?, holeDecl?) then checkHoleScope hole decl
  replaceMainGoal (state.goals.map (·.mvarId))

end Lean.Elab.Tactic.VCGen.Ascend
