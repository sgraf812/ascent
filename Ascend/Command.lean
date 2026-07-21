import Ascend.Frontend

/-!
# The `ascend_def` command

`ascend_def a from ⦃P⦄ (_ : AM AV) ⊑[γ] c ⦃Q; E⦄ by tac` synthesizes the abstract program into a
new definition `a`, then states and proves the refinement theorem `a.refines` against it,
discharging the verification conditions with `tac`. The concrete program's head definition is
unfolded to expose its structure.

This is AutoCorres' convert/define split: the engine *converts* (synthesizes the body and its
proof against the `_` hole), and the command *defines* (extracts the body into `a` and restates
the refinement against the new constant, which holds definitionally).
-/

open Lean Meta Sym Elab Command Term

namespace Ascend

syntax (name := ascendCmd) "ascend_def " ident " from " term
  (" by " tacticSeq)? : command

elab_rules : command
  | `(ascend_def $name from $stmt $[by $tac:tacticSeq]?) =>
    liftTermElabM do
      -- Elaborate the refinement statement; the `_` in the abstract-program position is the
      -- synthesis hole.
      let ty ← elabTerm stmt (mkSort .zero)
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars ty
      unless ty.isAppOfArity ``Ascent.RTriple 22 do
        throwError "ascend: the statement is not a refinement triple:{indentExpr ty}"
      let .mvar aId := ty.getAppArgs[13]!.getAppFn
        | throwError "ascend: the abstract program must be a hole `(_ : AM AV)`"
      -- Unfold exactly the concrete program's head definition to expose its structure.
      let unfoldNames := match ty.getAppArgs[14]!.getAppFn.constName? with
        | some c => #[c]
        | none => #[]
      -- Convert: synthesize the abstract program into `?a`, proving `ty` modulo the VCs.
      let proof ← mkFreshExprSyntheticOpaqueMVar ty
      let (vcs, finalize) ← mainWith proof.mvarId! unfoldNames
      -- Discharge the verification conditions.
      for vc in vcs do
        let some tac := tac
          | throwError "ascend: unsolved verification condition:\
              {indentExpr (← vc.getType)}\nprovide a `by` clause"
        let (rest, _) ← runTactic vc (← `(tactic| ($tac))).raw {} {}
        unless rest.isEmpty do
          throwError "ascend: `by` clause did not close the verification condition{
            indentExpr (← vc.getType)}"
      -- Define: extract the synthesized program into `name`.
      let a ← instantiateMVars (mkMVar aId)
      addDecl <| .defnDecl {
        name := name.getId, levelParams := [], type := ← inferType a, value := a,
        hints := .regular 0, safety := .safe }
      -- The refinement theorem against the new constant. `ty` still carries `?a` (it was
      -- instantiated before conversion assigned it); replacing that hole with the constant
      -- gives a statement definitionally equal to the proved one, so the proof term serves.
      let thmTy := ty.replace fun e =>
        if e.isMVar && e.mvarId! == aId then some (mkConst name.getId) else none
      addDecl <| .thmDecl {
        name := name.getId ++ `refines, levelParams := [], type := thmTy,
        value := finalize (← instantiateMVars proof) }

end Ascend
