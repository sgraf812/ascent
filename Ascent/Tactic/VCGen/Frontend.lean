import Lean.Elab.Tactic.VCGen.Frontend
import Ascent.Tactic.VCGen.Driver

/-!
# The `ascend'` tactic

`ascend'` runs the forked worklist on a goal `⦃P⦄ c ⪯[γ] a ⦃Q; E⦄`. The `wrp` goals use the
`@[ascend]` database, and the `wp` goals use the `@[spec]` database. A natural metavariable in
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

/-- Replace the delayed assignment of each hole in `e` by an ordinary one: `?h xs := ?b` becomes
`?h := fun xs => b`, where `b` is the value of `?b`. An unapplied occurrence of `?h`, such as the
continuation of a bind, needs the ordinary assignment. -/
partial def resolveDelayedHoles (e : Expr) : MetaM Unit := do
  for mv in ← getMVars e do
    let some d ← getDelayedMVarAssignment? mv | continue
    let b ← instantiateMVars (mkMVar d.mvarIdPending)
    resolveDelayedHoles b
    let b ← instantiateMVars b
    let val ← withLCtx' (← d.mvarIdPending.getDecl).lctx (mkLambdaFVars d.fvars b)
    modifyMCtx fun mctx => { mctx with dAssignment := mctx.dAssignment.erase mv }
    mv.assign val

/-- Restore the local context of the hole, and check that the synthesized program uses only the
free variables of that context. The unassigned metavariables of the program, which the run
emitted as sealed goals, take the same context. -/
def checkHoleScope (hole : MVarId) (decl : MetavarDecl) : MetaM Unit := do
  resolveDelayedHoles (← instantiateMVars (mkMVar hole))
  let restore (mv : MVarId) := modifyMCtx (·.modifyExprMVarDecl mv fun d =>
    { d with lctx := decl.lctx, localInstances := decl.localInstances })
  restore hole
  let val ← instantiateMVars (mkMVar hole)
  let outOfScope (e : Expr) := (e.find? fun e => e.isFVar && !decl.lctx.contains e.fvarId!).isSome
  if outOfScope val then
    throwError "ascend: the synthesized abstract program mentions a variable that the run \
      introduced, such as the concrete state"
  for mv in ← getMVars val do
    if outOfScope (← instantiateMVars (← mv.getType)) then
      throwError "ascend: a hole of the synthesized abstract program has a type that mentions a \
        variable that the run introduced"
    restore mv

@[tactic ascendTac]
def elabAscend : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let hole? ← unsealAbstractHole goal
  let holeDecl? ← hole?.mapM (·.getDecl)
  let thms ← vcgenSimpExt.getTheorems
  let simpMethods : Sym.Simp.Methods :=
    { pre := Sym.Simp.beta >> Sym.Simp.reduceProj >> Sym.Simp.reduceMatcher
      post := Sym.Simp.evalGround >> thms.rewrite }
  let ctx : Context :=
    { backwardRules := ← mkBackwardRules, simpMethods, internalize := false }
  let scope : Scope := { specs := ← getAscendSpecTheorems }
  let coreScope : Scope := { specs := ← getSpecTheorems }
  let params ← Grind.mkDefaultParams { clean := false }
  let (_, state) ← Grind.GrindTacticM.runAtGoal goal params (sym := true) do
    let g ← Lean.Elab.Tactic.Grind.getMainGoal
    let result ← Lean.Elab.Tactic.Grind.liftGrindM (run g ctx scope coreScope)
    Lean.Elab.Tactic.Grind.replaceMainGoal result.vcs.toList
  if let (some hole, some decl) := (hole?, holeDecl?) then checkHoleScope hole decl
  replaceMainGoal (state.goals.map (·.mvarId))

end Lean.Elab.Tactic.VCGen.Ascend
