import Ascend.RuleConstruction

/-!
# The main solve step

Runs once per worklist iteration and either decomposes the current goal into subgoals or
reports why no further progress is possible. Each strategy is a small function returning
`none` when its shape does not match; `solve` dispatches them in order.
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

/-- Strategy: introduce a `∀`/implication target, lifting rule-precondition hypotheses (such
as no-overflow guards) into the context. -/
private def forallIntro? (goal : MVarId) (target : Expr) : AscendM (Option MVarId) := do
  unless target.isForall do return none
  let (_, goal) ← goal.intros
  return some goal

/-- Strategy: unfold an `RTriple` target into its `le_rwp` field via the constructor. -/
private def rtripleIntro? (goal : MVarId) (target : Expr) : AscendM (Option MVarId) := do
  unless target.isAppOfArity ``Ascent.RTriple 22 do return none
  let [goal] ← goal.applyConst ``Ascent.RTriple.intro | return none
  return some goal

/-- Strategy: beta-reduce the right-hand side of the entailment; rebound couplings arrive as
`(fun av cv => …) v c` after a leaf consumes them. -/
private def rhsBeta? (goal : MVarId) (relHead : Expr) (relArgs : Array Expr) :
    AscendM (Option MVarId) := do
  let rhs := relArgs[3]!
  unless rhs.getAppFn.isLambda do return none
  let target := mkApp4 relHead relArgs[0]! relArgs[1]! relArgs[2]! rhs.headBeta
  return some (← goal.replaceTargetDefEq target)

/-- Strategy: beta-reduce the program head; continuations arrive as `c₂ cv`. -/
private def progBeta? (goal : MVarId) (g : RWPApp) : AscendM (Option MVarId) := do
  unless g.c.getAppFn.isLambda do return none
  let rhs := mkAppN g.head (g.args.set! 18 g.c.headBeta)
  let target := mkApp4 g.relHead g.relArgs[0]! g.relArgs[1]! g.pre rhs
  return some (← goal.replaceTargetDefEq target)

/-- Strategy: apply a registered spec for the program, most specific first. -/
private def applySpec (goal : MVarId) (g : RWPApp) : AscendM SolveResult := do
  let mut cands ← (← read).specs.getMatch g.c
  cands := cands.qsort fun s₁ s₂ => s₁.specificity > s₂.specificity
  for spec in cands do
    if let some ng ← applyRule goal g spec then
      return .goals [ng]
  return .stop (.noSpecFound g.c)

/-- Strategy: split a conjunction on the right, at the `Prop` lattice. -/
private def andSplit? (goal : MVarId) (relHead : Expr) (relArgs : Array Expr) :
    AscendM (Option (List MVarId)) := do
  let rhs := relArgs[3]!
  unless rhs.isAppOfArity ``And 2 do return none
  let pre := relArgs[2]!
  let A := rhs.getAppArgs[0]!
  let B := rhs.getAppArgs[1]!
  let ngA ← mkFreshExprSyntheticOpaqueMVar (mkApp4 relHead relArgs[0]! relArgs[1]! pre A)
  let ngB ← mkFreshExprSyntheticOpaqueMVar (mkApp4 relHead relArgs[0]! relArgs[1]! pre B)
  goal.assign (mkApp5 (mkConst ``Ascend.prop_le_and) pre A B ngA ngB)
  return some [ngA.mvarId!, ngB.mvarId!]

/-- Strategy: introduce an implication on the right, at the `Prop` lattice; the hypothesis
(a guard, or an established coupling) reaches the context through `forallIntro?`. -/
private def impIntro? (goal : MVarId) (relHead : Expr) (relArgs : Array Expr) :
    AscendM (Option MVarId) := do
  let rhs := relArgs[3]!
  unless rhs.isArrow do return none
  let pre := relArgs[2]!
  let A := rhs.bindingDomain!
  let B := rhs.bindingBody!
  let inner := mkApp4 relHead relArgs[0]! relArgs[1]! pre B
  let ng ← mkFreshExprSyntheticOpaqueMVar (← mkArrow A inner)
  goal.assign (mkApp4 (mkConst ``Ascend.prop_le_imp) pre A B ng)
  return some ng.mvarId!

/-- Strategy: close a reflexive equation on the right. -/
private def eqRefl? (goal : MVarId) (relArgs : Array Expr) : AscendM (Option Unit) := do
  let rhs := relArgs[3]!
  unless rhs.isAppOfArity ``Eq 3 do return none
  let args := rhs.getAppArgs
  unless args[1]! == args[2]! do return none
  let u ← getLevel args[0]!
  goal.assign (mkApp3 (mkConst ``Ascend.prop_le_eq_refl [u]) relArgs[2]! args[0]! args[1]!)
  return some ()

/-- Strategy: close against a hypothesis, such as a coupling established by an earlier leaf. -/
private def hypClose? (goal : MVarId) (relArgs : Array Expr) : AscendM (Option Unit) := do
  let rhs := relArgs[3]!
  let some hyp := (← getLCtx).findDecl? fun d =>
    if !d.isImplementationDetail && d.type == rhs then some d else none
    | return none
  goal.assign (mkApp3 (mkConst ``Ascend.prop_le_of) relArgs[2]! rhs hyp.toExpr)
  return some ()

/--
One solve step, dispatching the strategies in order: introduce `∀`/implication targets, unfold
an `RTriple` target, then on `pre ⊑ rhs` beta-reduce the right-hand side, decompose an `rwp`
application through the registered specs, and decompose the `Prop`-lattice connectives of spec
preconditions.
-/
def solve (goal : MVarId) : AscendM SolveResult := goal.withContext do
  let target ← goal.getType
  if let some goal ← forallIntro? goal target then return .goals [goal]
  if let some goal ← rtripleIntro? goal target then return .goals [goal]
  let some (relHead, relArgs) := parseRel? target
    | return .stop (.noEntailment target)
  if let some goal ← rhsBeta? goal relHead relArgs then return .goals [goal]
  if let some g := parseRWP? target then
    if let some goal ← progBeta? goal g then return .goals [goal]
    return ← applySpec goal g
  -- The carrier may be `Sort ?u` with `?u` assigned: rules applied with fresh level
  -- metavariables leave assigned-but-unsubstituted levels in the targets they build.
  if (← instantiateMVars relArgs[0]!).isProp then
    if let some goals ← andSplit? goal relHead relArgs then return .goals goals
    if let some goal ← impIntro? goal relHead relArgs then return .goals [goal]
    if let some _ ← eqRefl? goal relArgs then return .goals []
    if let some _ ← hypClose? goal relArgs then return .goals []
  return .stop (.noProgress relArgs[2]! relArgs[3]!)

end Ascend
