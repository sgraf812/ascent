import Ascend.Context
import Ascend.Rules

/-!
# Rule application

One mechanism applies every registered rule, structural or leaf, all of which are `RTriple`
theorems with any recursive `rwp` occurrence confined to the precondition:

1. Instantiate the rule's telescope with fresh metavariables and project the `RTriple`
   conclusion through `le_rwp`, giving a proof of `pre' ⊑ rwp γ' a' c' Q' E'`.
2. When the goal's abstract slot is a flex application `?m t₁ … tₖ`, assign
   `?m := fun x₁ … xₖ => a'[avᵢ ↦ xᵢ]`, the rule's abstract program with its abstract-input
   metavariables abstracted. The goal's abstract side then beta-reduces to `a'` with `avᵢ`
   unified against `tᵢ`, so the flex application never reaches the unifier.
3. `isDefEq` the rule's `rwp` application against the goal's. This instantiates the abstract
   program (synthesis), the couplings `Q'`/`E'` (auto-framing: the goal's rebound continuation
   passes through untouched), the value types and instances, and validates the concrete match.
4. Synthesize any instance metavariables the conclusion did not determine.
5. Close the goal with `rel_trans`, leaving `pre ⊑ pre'` as the sole subgoal: the rule's
   precondition, carrying the rest of the chain.
-/

open Lean Meta

namespace Ascend

/-- Run `k`; on failure or a `none` result, roll back all state (including metavariable
assignments). -/
def commitWhenSome? (k : AscendM (Option α)) : AscendM (Option α) := do
  let s ← (saveState : MetaM Meta.SavedState)
  try
    match ← k with
    | some a => return some a
    | none => s.restore; return none
  catch _ =>
    s.restore
    return none

/-- The rule's conclusion as an entailment `pre' ⊑ rwp …` together with its proof: an
`RTriple` conclusion projects through `le_rwp`. -/
private def conclusionProof (rule : Expr) (mvs : Array Expr) (concl : Expr) :
    MetaM (Option (Expr × Expr)) := do
  if concl.isAppOfArity ``Ascent.RTriple 22 then
    let leRwp ← mkConstWithFreshMVarLevels ``Ascent.RTriple.le_rwp
    let prf := mkAppN leRwp (concl.getAppArgs.push (mkAppN rule mvs))
    return some (← inferType prf, prf)
  if concl.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
    return some (concl, mkAppN rule mvs)
  return none

/-- Assign the goal's flex abstract slot `?m t₁ … tₖ` the rule's abstract template with the
abstract-input metavariables `avMVars` abstracted. A bare metavariable (`k = 0`) needs no
template; the `isDefEq` step assigns it directly. -/
private def assignAbstractTemplate (goalA : Expr) (ruleA : Expr) (avMVars : Array Expr) :
    MetaM Bool := do
  let .mvar mvarId := goalA.getAppFn | return false
  let ts := goalA.getAppArgs
  if ts.isEmpty then
    return true
  unless ts.size == avMVars.size do return false
  let decls ← avMVars.mapM fun av => return (`x, fun _ => inferType av)
  let lam ← withLocalDeclsD decls fun xs => do
    let template := ruleA.replace fun e =>
      avMVars.idxOf? e |>.map fun i => xs[i]!
    mkLambdaFVars xs template
  mvarId.assign lam
  return true

/-- Apply the registered rule `spec` to a goal `pre ⊑ rwp γ a c Q E`. Returns the
`pre ⊑ pre'` subgoal, or `none` (state rolled back) if the rule does not apply. -/
def applyRule (goal : MVarId) (g : RWPApp) (spec : SpecInfo) : AscendM (Option MVarId) := do
  commitWhenSome? do
    let rule ← mkConstWithFreshMVarLevels spec.declName
    -- Non-reducing: at the `Prop` lattice the `RTriple` conclusion would reduce to an
    -- implication and the telescope would consume the precondition as a binder.
    let (mvs, bis, concl) ← forallMetaTelescope (← inferType rule)
    let some (relTy, rulePrf) ← conclusionProof rule mvs concl | return none
    let some ruleRwp := parseRWP? relTy | return none
    let goalA ← instantiateMVarsIfMVarApp g.a
    if goalA.getAppFn.isMVar then
      unless ← assignAbstractTemplate goalA ruleRwp.a (spec.avPositions.map (mvs[·]!)) do
        return none
    unless ← isDefEq ruleRwp.rhs g.rhs do return none
    -- Instances the conclusion did not determine (e.g. `WPMonadExact`, `Frame`).
    for mv in mvs, bi in bis do
      if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
        mv.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType mv)))
    -- The subgoal embeds the rule's precondition, which the assignments above just filled in.
    let pre' ← instantiateMVars ruleRwp.pre
    let newTarget := mkApp4 g.relHead g.relArgs[0]! g.relArgs[1]! g.pre pre'
    let ng ← mkFreshExprSyntheticOpaqueMVar newTarget
    let relTrans := mkConst ``Lean.Order.PartialOrder.rel_trans g.relHead.constLevels!
    goal.assign <| mkApp7 relTrans g.relArgs[0]! g.relArgs[1]! g.pre pre' g.rhs ng rulePrf
    return some ng.mvarId!

end Ascend
