import Ascend.Context
import Ascend.Rules

/-!
# Rule application

One mechanism applies both the structural `rwp_bind` law and registered `@[ascend]` specs, all
of which are triples with any recursive `rwp` occurrence confined to the precondition:

1. Instantiate the rule's telescope with fresh metavariables and unfold its `RTriple`
   conclusion one definitional step, giving `pre' ⊑ rwp γ' a' c' Q' E'`.
2. When the goal's abstract slot is a flex application `?m t₁ … tₖ`, assign
   `?m := fun x₁ … xₖ => a'[avᵢ ↦ xᵢ]`, the rule's abstract program with its abstract-input
   metavariables abstracted. The goal's abstract side then beta-reduces to `a'` with `avᵢ`
   unified against `tᵢ`, so the flex application never reaches the unifier.
3. `isDefEq` the rule's `rwp` application against the goal's. This instantiates the abstract
   program (synthesis), the couplings `Q'`/`E'` (auto-framing: the goal's rebound continuation
   passes through untouched), the value types and instances, and validates the concrete match.
4. Synthesize any instance metavariables the conclusion did not determine.
5. Close the goal with `rel_trans`, leaving `pre ⊑ pre'` as the sole subgoal: for `rwp_bind`
   the head's `rwp`, for a leaf the spec's precondition.
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

/-- The rule's conclusion in `pre' ⊑ rwp …` form: an `RTriple` conclusion is unfolded one
definitional step. -/
private def conclusionAsRel (concl : Expr) : MetaM (Option (Array Expr)) := do
  let concl ← if concl.isAppOfArity ``Ascent.RTriple 22 then
    match ← unfoldDefinition? concl with
    | some e => pure e
    | none => return none
  else
    pure concl
  return parseRel? concl |>.map (·.2)

/-- Assign the goal's flex abstract slot `?m t₁ … tₖ` the rule's abstract template with the
abstract-input metavariables `avMVars` abstracted. -/
private def assignAbstractTemplate (goalA : Expr) (ruleA : Expr) (avMVars : Array Expr) :
    MetaM Bool := do
  let .mvar mvarId := goalA.getAppFn | return false
  let ts := goalA.getAppArgs
  unless ts.size == avMVars.size do return false
  if ts.isEmpty then
    return true  -- bare metavariable; the isDefEq step assigns it directly
  let decls ← avMVars.mapM fun av => return (`x, fun _ => inferType av)
  let lam ← withLocalDeclsD decls fun xs => do
    let template := ruleA.replace fun e =>
      avMVars.idxOf? e |>.map fun i => xs[i]!
    mkLambdaFVars xs template
  mvarId.assign lam
  return true

/--
Apply the rule `declName` to a goal `pre ⊑ rwp γ a c Q E`. `avPositions` are the telescope
positions of the rule's abstract-input variables (empty for `rwp_bind` and seed specs).
Returns the `pre ⊑ pre'` subgoal, or `none` (state rolled back) if the rule does not apply.
-/
def applyRule (goal : MVarId) (g : RWPApp) (declName : Name) (avPositions : Array Nat) :
    AscendM (Option MVarId) := do
  commitWhenSome? do
    let rule ← mkConstWithFreshMVarLevels declName
    -- Non-reducing: at the `Prop` lattice the `RTriple` conclusion would reduce to an
    -- implication and the telescope would consume the precondition as a binder.
    let (mvs, bis, concl) ← forallMetaTelescope (← inferType rule)
    let some cArgs ← conclusionAsRel concl | return none
    let pre' := cArgs[2]!
    let rhs' := cArgs[3]!
    let some ruleRwp := parseRWP? (mkApp4 g.relHead cArgs[0]! cArgs[1]! pre' rhs') | return none
    -- Pre-assign the flex abstract slot from the rule's template.
    let goalA ← instantiateMVars g.a
    if goalA.getAppFn.isMVar then
      unless ← assignAbstractTemplate goalA ruleRwp.a (avPositions.map (mvs[·]!)) do
        return none
    unless ← isDefEq rhs' g.rhs do return none
    -- Instances the conclusion did not determine (e.g. `WPMonadExact`, `Frame`).
    for mv in mvs, bi in bis do
      if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
        mv.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType mv)))
    let pre' ← instantiateMVars pre'
    let newTarget := mkApp4 g.relHead g.relArgs[0]! g.relArgs[1]! g.pre pre'
    let ng ← mkFreshExprSyntheticOpaqueMVar newTarget
    let relTrans := mkConst ``Lean.Order.PartialOrder.rel_trans g.relHead.constLevels!
    let proof := mkApp7 relTrans g.relArgs[0]! g.relArgs[1]! g.pre pre' g.rhs
      ng (mkAppN rule mvs)
    goal.assign proof
    return some ng.mvarId!

end Ascend
