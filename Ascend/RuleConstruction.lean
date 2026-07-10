import Ascend.Context
import Ascend.Rules

/-!
# Rule compilation and application

A registered spec is compiled once per phase into an apply-ready backward rule, and applied
per goal by pattern matching, so no application-time work scales with the size of the goal's
value terms.

**Compilation** (`compileRule`, cached by spec name and the goal's `WP` instances): project
the spec's `RTriple` conclusion through `le_rwp` to `pre' ⊑ rwp …`; pin the phase against the
goal (the assertion lattices, `γ`, and the monads, read off the goal's `rwp` arguments);
synthesize the instances the conclusion does not determine; wrap the transitivity composition
as the auxiliary theorem `∀ params P', (P' ⊑ pre') → P' ⊑ rwp …`; abstract the remaining
parameters (the value slots) into a `BackwardRule`.

**Application** (`applyRule`): when the goal's abstract slot is a flex application
`?m t₁ … tₖ`, first assign `?m` the spec's abstract template (a lambda over its abstract
inputs, other parameters fresh) and rebuild the target with the application beta-reduced, so
the slot is rigid. Then `BackwardRule.apply` matches the conclusion — binding the value slots,
the couplings (auto-framing), and any goal-side metavariables by match-unification — and
leaves the precondition entailment `pre ⊑ pre'` as the sole subgoal.
-/

open Lean Meta Sym

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
    return some (← Meta.inferType prf, prf)
  if concl.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
    return some (concl, mkAppN rule mvs)
  return none

/-- The `rwp` argument positions that identify a phase: the assertion lattices and their
instances, `Ξ`, `HasEPost`, and `γ`. The program and value types (and with them the `WP`
instances) stay parametric, so one compiled rule serves every node of a chain. -/
private def phasePositions : Array Nat := #[4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16]

/-- Compile `spec` to apply-ready form against the phase of the goal `g`. -/
private def compileRule (si : SpecInfo) (g : RWPApp) : AscendM (Option CachedRule) := do
  let rule ← mkConstWithFreshMVarLevels si.declName
  -- Non-reducing: at the `Prop` lattice the `RTriple` conclusion would reduce to an
  -- implication and the telescope would consume the precondition as a binder.
  let (mvs, bis, concl) ← forallMetaTelescope (← Meta.inferType rule)
  let some (relTy, prf) ← conclusionProof rule mvs concl | return none
  let some ruleRwp := parseRWP? relTy | return none
  -- Pin the phase, and the monads (the proof-only instances depend on them).
  for i in phasePositions do
    unless ← isDefEqGuarded ruleRwp.args[i]! g.args[i]! do return none
  unless ← isDefEqGuarded ruleRwp.AProg.getAppFn g.AProg.getAppFn do return none
  unless ← isDefEqGuarded ruleRwp.CProg.getAppFn g.CProg.getAppFn do return none
  for mv in mvs, bi in bis do
    if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
      mv.mvarId!.assign (← Meta.synthInstance (← instantiateMVars (← Meta.inferType mv)))
  -- The abstract template, before `abstractMVars` retires the telescope metavariables.
  let template? ← do
    if si.avPositions.isEmpty then
      pure none
    else
      let avMVars := si.avPositions.map (mvs[·]!)
      let decls ← avMVars.mapM fun av => do
        let ty ← Meta.inferType av
        return (`x, fun (_ : Array Expr) => (pure ty : AscendM Expr))
      let lam ← withLocalDeclsD decls fun xs => do
        let a ← instantiateMVars ruleRwp.a
        mkLambdaFVars xs <| a.replace fun e => avMVars.idxOf? e |>.map (xs[·]!)
      pure (some (← abstractMVars lam))
  -- The auxiliary theorem `∀ P', (P' ⊑ pre') → P' ⊑ rwp …`.
  let relTy ← instantiateMVars relTy
  let some (relHead, relArgs) := parseRel? relTy | return none
  let pre' := relArgs[2]!
  let aux ← withLocalDeclD `P' (← instantiateMVars g.CPred) fun P' => do
    withLocalDeclD `h (mkApp4 relHead relArgs[0]! relArgs[1]! P' pre') fun h => do
      let relTrans := mkConst ``Lean.Order.PartialOrder.rel_trans relHead.constLevels!
      mkLambdaFVars #[P', h] <|
        mkApp7 relTrans relArgs[0]! relArgs[1]! P' pre' relArgs[3]! h (← instantiateMVars prf)
  let res ← abstractMVars aux
  let rule ← mkBackwardRuleFromExpr res.expr res.paramNames.toList
  return some { rule, template? }

/-- The compiled rule for `spec` against the phase of `g`, from the cache or compiled now. -/
private def cachedRule (si : SpecInfo) (g : RWPApp) : AscendM (Option CachedRule) := do
  let key := (si.declName, ExprPtr.mk g.γ)
  if let some c := (← get).ruleCache[key]? then return some c
  let some c ← compileRule si g | return none
  modify fun s => { s with ruleCache := s.ruleCache.insert key c }
  return some c

/-- Assign a flex abstract slot `?m t₁ … tₖ` from the spec's template and rebuild the target
with the slot beta-reduced, so pattern matching sees a rigid program. Returns the updated
goal, or `none` when the slot is already rigid (nothing to do). -/
private def fixAbstractSlot? (goal : MVarId) (g : RWPApp) (c : CachedRule) :
    AscendM (Option (Option MVarId)) := do
  let goalA ← instantiateMVarsIfMVarApp g.a
  let .mvar mvarId := goalA.getAppFn | return some none
  -- Substitute the value arguments now: rule application binds by metavariable assignment, so
  -- an uninstantiated value is an assigned-mvar chain that every later inspection would
  -- re-walk. The previous leaf cleaned its prefix, so this is one layer per leaf.
  let ts ← goalA.getAppArgs.mapM (instantiateMVars ·)
  if ts.isEmpty then return some none
  let some tmpl := c.template? | return none
  let (_, _, lam) ← openAbstractMVarsResult tmpl
  unless lam.isLambda do return none
  mvarId.assign lam
  let a ← shareCommonInc (lam.beta ts)
  let rhs := mkAppN g.head (g.args.set! 17 a)
  let target := mkApp4 g.relHead g.relArgs[0]! g.relArgs[1]! g.pre rhs
  return some (some (← goal.replaceTargetDefEq (← shareCommonInc target)))

/-- Apply the registered rule `si` to a goal `pre ⊑ rwp γ a c Q E`. Returns the `pre ⊑ pre'`
subgoal, or `none` (state rolled back) if the rule does not apply. -/
def applyRule (goal : MVarId) (g : RWPApp) (si : SpecInfo) : AscendM (Option MVarId) := do
  commitWhenSome? do
    let some c ← cachedRule si g | return none
    let some goal? ← fixAbstractSlot? goal g c | return none
    let goal := goal?.getD goal
    let .goals [ng] ← c.rule.apply goal | return none
    return some ng

end Ascend
