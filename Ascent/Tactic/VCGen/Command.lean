import Ascent.Tactic.VCGen.Frontend

/-!
# The `ascend_def` command

`ascend_def a : T from ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄ by tac` defines `a : T` as the abstract program that
`ascend` synthesizes for `c`, and proves the refinement as the theorem `a.refines`. In the
statement, `a` is a variable of type `T`. The command replaces `a` by a synthesis hole, runs
`ascend` with the head definition of `c` unfolded, and closes each VC with `tac`.
-/

open Lean Meta Elab Command Term

namespace Lean.Elab.Tactic.VCGen.Ascend

syntax (name := ascendDefCmd)
  "ascend_def " ident " : " term " from " term (" by " tacticSeq)? : command

/-- The head constant of the concrete program `c`, if `ascend` can unfold it: a definition that
is neither a projection nor an instance. -/
def unfoldableHead? (c : Expr) : MetaM (Option Name) := do
  let some declName := c.getAppFn.constName? | return none
  let env ← getEnv
  let some (.defnInfo _) := env.find? declName | return none
  if env.isProjectionFn declName || (← isInstance declName) then return none
  return some declName

elab_rules : command
  | `(ascend_def $name : $type from $stmt $[by $tac?]?) => liftTermElabM do
    let T ← elabType type
    synthesizeSyntheticMVarsNoPostponing
    let stmtFn ← withLocalDeclD name.getId T fun x => do
      let e ← elabType stmt
      synthesizeSyntheticMVarsNoPostponing
      mkLambdaFVars #[x] (← instantiateMVars e)
    let hole ← mkFreshExprMVar T
    let goalType := stmtFn.beta #[hole]
    unless goalType.isAppOfArity ``Ascent.Refinement 22 do
      throwError "ascend_def: the statement is not a refinement:{indentExpr goalType}"
    let proof ← mkFreshExprSyntheticOpaqueMVar goalType
    let ascendStx ← match ← unfoldableHead? goalType.getAppArgs[13]! with
      | some declName => `(tactic| ascend [$(mkIdent declName):ident])
      | none => `(tactic| ascend)
    let (vcs, _) ← Lean.Elab.runTactic proof.mvarId! ascendStx
    for vc in vcs do
      let some tac := tac?
        | throwError "ascend_def: unsolved verification condition:{indentExpr (← vc.getType)}\n\
            provide a `by` clause"
      let (rest, _) ← Lean.Elab.runTactic vc (← `(tactic| ($tac)))
      unless rest.isEmpty do
        throwError "ascend_def: the `by` clause leaves the verification condition\
          {indentExpr (← vc.getType)}"
    let value ← instantiateMVars hole
    if value.hasMVar then
      throwError "ascend_def: the synthesized program has holes:{indentExpr value}"
    addDecl <| .defnDecl {
      name := name.getId, levelParams := [], type := T, value,
      hints := .regular 0, safety := .safe }
    let proof ← instantiateMVars proof
    if proof.hasMVar then
      throwError "ascend_def: the refinement proof has holes"
    addDecl <| .thmDecl {
      name := name.getId ++ `refines, levelParams := [],
      type := stmtFn.beta #[mkConst name.getId], value := proof }

end Lean.Elab.Tactic.VCGen.Ascend
