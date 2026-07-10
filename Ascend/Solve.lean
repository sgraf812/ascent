import Ascend.RuleConstruction

/-!
# The main solve step

Runs once per worklist iteration and either decomposes the current goal into subgoals or
reports why no further progress is possible.
-/

open Lean Meta

namespace Ascend

/-- Why no further progress is possible on the current goal. -/
inductive StopReason where
  /-- The target is not of the form `pre ⊑ rhs`. -/
  | noEntailment (target : Expr)
  /-- No registered spec matched the program `c`. -/
  | noSpecFound (c : Expr)
  /-- The target is `pre ⊑ rhs` but no strategy applies. -/
  | noProgress (pre rhs : Expr)

/-- The result of one solve step. -/
inductive SolveResult where
  /-- The goal was decomposed into these subgoals. -/
  | goals (subgoals : List MVarId)
  /-- No further progress; emit the goal as a VC. -/
  | stop (reason : StopReason)

/-- Rebuild the target `pre ⊑ rwp … c …` with a new, definitionally equal program `c`. -/
private def replaceProgDefEq (goal : MVarId) (g : RWPApp) (c : Expr) : MetaM MVarId := do
  let rhs := mkAppN g.head (g.args.set! 18 c)
  let target := mkApp4 g.relHead g.relArgs[0]! g.relArgs[1]! g.pre rhs
  goal.replaceTargetDefEq target

/-- Decompose a weakest-precondition goal `pre ⊑ rwp γ a c Q E`: beta-reduce the program head,
apply `rwp_bind` at a bind, or apply a registered spec at a leaf. -/
private def solveRWP (goal : MVarId) (g : RWPApp) : AscendM SolveResult := do
  -- Reduce a beta redex at the program head (continuations arrive as `c₂ cv`).
  let c := g.c
  if c.getAppFn.isLambda then
    return .goals [← replaceProgDefEq goal g c.headBeta]
  let a ← instantiateMVars g.a
  -- A bind decomposes structurally when the abstract side is still an unapplied hole.
  if c.isAppOfArity ``Bind.bind 6 && a.isMVar then
    if let some ng ← applyRule goal g ``Ascent.rwp_bind #[] then
      return .goals [ng]
  -- Leaf: registered specs, most specific first.
  let mut cands ← (← read).specs.getMatch c
  cands := cands.qsort fun s₁ s₂ => s₁.specificity > s₂.specificity
  for spec in cands do
    if let some ng ← applyRule goal g spec.declName spec.avPositions then
      return .goals [ng]
  return .stop (.noSpecFound c)

/--
One solve step, dispatching on the target's shape:

1. A `∀`/implication target is introduced (lifting spec-precondition hypotheses like
   no-overflow guards into the context).
2. An `RTriple` target unfolds to its `pre ⊑ rwp …` form.
3. On `pre ⊑ rhs`: beta-reduce `rhs` (rebound couplings arrive as `(fun av cv => …) v c`);
   decompose an `rwp` application (bind/leaf); split `∧` and introduce `→` at the `Prop`
   lattice; close a reflexive equation.
-/
def solve (goal : MVarId) : AscendM SolveResult := goal.withContext do
  -- No entry instantiation: every target the engine constructs is built instantiated, and a
  -- full traversal here would re-walk the embedded continuation at every step.
  let target ← goal.getType
  if target.isForall then
    let (_, goal) ← goal.intros
    return .goals [goal]
  if target.isAppOfArity ``Ascent.RTriple 22 then
    let some target' ← unfoldDefinition? target
      | return .stop (.noEntailment target)
    return .goals [← goal.replaceTargetDefEq target']
  let some (relHead, relArgs) := parseRel? target
    | return .stop (.noEntailment target)
  let pre := relArgs[2]!
  let rhs := relArgs[3]!
  -- Beta-reduce the RHS: the rebound coupling applied to a leaf's values.
  if rhs.getAppFn.isLambda then
    let target := mkApp4 relHead relArgs[0]! relArgs[1]! pre rhs.headBeta
    return .goals [← goal.replaceTargetDefEq target]
  if let some g := parseRWP? target then
    return ← solveRWP goal g
  -- Prop-lattice decomposition of spec preconditions.
  if relArgs[0]!.isProp then
    if rhs.isAppOfArity ``And 2 then
      let A := rhs.getAppArgs[0]!
      let B := rhs.getAppArgs[1]!
      let ngA ← mkFreshExprSyntheticOpaqueMVar (mkApp4 relHead relArgs[0]! relArgs[1]! pre A)
      let ngB ← mkFreshExprSyntheticOpaqueMVar (mkApp4 relHead relArgs[0]! relArgs[1]! pre B)
      goal.assign (mkApp5 (mkConst ``Ascend.prop_le_and) pre A B ngA ngB)
      return .goals [ngA.mvarId!, ngB.mvarId!]
    if rhs.isArrow then
      let A := rhs.bindingDomain!
      let B := rhs.bindingBody!
      let inner := mkApp4 relHead relArgs[0]! relArgs[1]! pre B
      let ng ← mkFreshExprSyntheticOpaqueMVar (← mkArrow A inner)
      goal.assign (mkApp4 (mkConst ``Ascend.prop_le_imp) pre A B ng)
      return .goals [ng.mvarId!]
    if rhs.isAppOfArity ``Eq 3 then
      let args := rhs.getAppArgs
      if args[1]! == args[2]! then
        let u ← getLevel args[0]!
        goal.assign (mkApp3 (mkConst ``Ascend.prop_le_eq_refl [u]) pre args[0]! args[1]!)
        return .goals []
    -- Close against a hypothesis: couplings established by earlier leaves.
    let hyp? := (← getLCtx).findDecl? fun d =>
      if !d.isImplementationDetail && d.type == rhs then some d else none
    if let some hyp := hyp? then
      goal.assign (mkApp3 (mkConst ``Ascend.prop_le_of) pre rhs hyp.toExpr)
      return .goals []
  return .stop (.noProgress pre rhs)

end Ascend
