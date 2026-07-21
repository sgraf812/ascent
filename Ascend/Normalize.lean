import Ascend.Lattice

/-!
# Precondition normalization and lifted-hypothesis discharge

The solve-time counterpart to `splitLatticeOp?`: once a connective is decomposed, the residual
`pre ⊑ rhs` is driven toward `⊤ ⊑ rhs` by lifting pure content (`⌜φ⌝` or a bare `Prop`) into the
local context, and a residual `⌜φ⌝` goal is discharged against the most recently lifted
hypothesis in `O(1)`. The backward rules are reused from `vcgen`; only the `AscendM` dispatch and
the `Scope` threading are ours.
-/

open Lean Meta Sym
open Lean.Elab.Tactic.Do.Internal

namespace Ascend

/-- Introduce the goal's leading binders, returning the innermost goal, the last introduced
fvar, and its instantiated type (the freshly lifted hypothesis). -/
def introLastHyp (goal : MVarId) : AscendM (MVarId × FVarId × Expr) := do
  let .goal decls goal ← Sym.intros goal | throwError "ascend: failed to intro lifted hypothesis"
  let some fv := decls.back? | throwError "ascend: intro produced no hypothesis"
  let ty ← goal.withContext do instantiateMVars (← fv.getType)
  return (goal, fv, ty)

/-- Apply a precondition-intro backward rule and introduce the lifted hypothesis. -/
def introPre (rule : BackwardRule) (goal : MVarId) : AscendM (MVarId × FVarId × Expr) := do
  let .goals [goal] ← rule.apply goal | throwError "ascend: precondition intro rule did not apply"
  introLastHyp goal

/-- Cancel a redundant `P ⊓ ⊤` precondition via `meet_top_le_of_le`, leaving `P ⊑ rhs`. Such a
precondition arises when `le_himp` splits `⊤ ⊑ a ⇨ b` into `a ⊓ ⊤ ⊑ b`. -/
def stripMeetTopPre? (goal : MVarId) (pre : Expr) : AscendM (Option MVarId) := do
  let_expr Lean.Order.meet _ _ _ top := pre | return none
  unless top.isAppOf ``Lean.Order.top do return none
  let .goals [g] ← (← read).backwardRules.meetTop.apply goal | return none
  return some g

/-- Lift an embedded pure precondition `⌜φ⌝` into the local context via `ofProp_le`, leaving `⊤`
as the residual precondition. -/
def ofPropPreIntro? (goal : MVarId) (pre : Expr) : AscendM (Option (MVarId × FVarId × Expr)) := do
  let_expr Lean.Order.CompleteLattice.ofProp _ _ φ := pre | return none
  if φ.isTrue then return none
  return some (← introPre (← read).backwardRules.ofPropPreIntro goal)

/-- Move a bare `Prop` precondition into the local context via `le_of_imp_top_le`, leaving `⊤`. -/
def barePreIntro? (goal : MVarId) (α pre : Expr) : AscendM (Option (MVarId × FVarId × Expr)) := do
  unless α.isProp do return none
  if pre.isAppOf ``Lean.Order.top then return none
  return some (← introPre (← read).backwardRules.propPreIntro goal)

/-- Replace a `True` precondition by `⊤` via `true_le_of_top_le`, or reduce a lifted `⊤ s₁ … sₙ`
precondition to the bare `⊤`. -/
def normalizePreToTop? (goal : MVarId) (pre target : Expr) : AscendM (Option MVarId) := do
  if pre.isTrue then
    let .goals [g] ← (← read).backwardRules.truePreIntro.apply goal | return none
    return some g
  VCGen.reduceTopAppliedPre? goal target pre

/-- Drive the precondition of `pre ⊑ rhs` toward `⊤`, lifting pure content into the local context
and recording any lifted hypothesis in the scope. -/
def normalizePre? (scope : Scope) (goal : MVarId) (α pre target : Expr) :
    AscendM (Option (Scope × List MVarId)) := do
  if let some g ← stripMeetTopPre? goal pre then
    return some (scope, [g])
  if let some (g, h, ty) ← ofPropPreIntro? goal pre then
    return some ({ scope with lastLiftedPre? := some (h, ty) }, [g])
  if let some g ← normalizePreToTop? goal pre target then
    return some (scope, [g])
  if let some (g, h, ty) ← barePreIntro? goal α pre then
    return some ({ scope with lastLiftedPre? := some (h, ty) }, [g])
  return none

/-- The most recently lifted pure precondition whose type is definitionally the residual `rhs`. -/
def liftedPreFor? (scope : Scope) (rhs : Expr) : AscendM (Option FVarId) := do
  let some (fv, ty) := scope.lastLiftedPre? | return none
  if ← isDefEqS ty rhs then return some fv else return none

/-- Close a residual `pre ⊑ ⌜φ⌝` at the `Prop` carrier against the most recently lifted
hypothesis via `le_of_right`. -/
def liftedHyp? (scope : Scope) (goal : MVarId) (α pre rhs : Expr) : AscendM (Option Unit) := do
  unless α.isProp do return none
  let some fv ← liftedPreFor? scope rhs | return none
  goal.assign (mkApp3 (mkConst ``Lean.Order.le_of_right) pre rhs (.fvar fv))
  return some ()

/-- Close a bare `Prop` residual against the most recently lifted hypothesis. -/
def liftedHypBare? (scope : Scope) (goal : MVarId) (target : Expr) : AscendM (Option Unit) := do
  let some fv ← liftedPreFor? scope target | return none
  goal.assign (.fvar fv)
  return some ()

/-- Close a reflexive entailment `pre ⊑ pre` via `PartialOrder.rel_refl`. -/
def rfl? (goal : MVarId) : AscendM (Option (List MVarId)) := do
  match ← (← read).backwardRules.refl.apply goal with
  | .goals gs => return some gs
  | _ => return none

/-- Strip a `(⊤ : Prop) ⊑ ·` wrapper from a VC via `top_le_prop`, leaving the bare proposition. -/
def elimTopPre (goal : MVarId) : AscendM MVarId := do
  let some (.sort .zero, _, pre, _) := (← instantiateMVarsIfMVarAppS (← goal.getType)).app4? ``Lean.Order.PartialOrder.rel
    | return goal
  unless (← instantiateMVarsIfMVarAppS pre).isAppOf ``Lean.Order.top do return goal
  match ← (← read).backwardRules.elimPre.apply goal with
  | .goals [g] => return g
  | _ => return goal

end Ascend
