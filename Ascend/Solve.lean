import Ascend.RuleConstruction

/-!
# The main solve step

Runs once per worklist iteration and either decomposes the current goal into subgoals or
reports why no further progress is possible. Each strategy is a small function returning
`none` when its shape does not match; `solve` dispatches them in order.
-/

open Lean Meta Sym

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
  let .goal _ goal ← Sym.intros goal | return none
  return some goal

/-- Strategy: unfold an `RTriple` target into its `le_rwp` field via the constructor. -/
private def rtripleIntro? (goal : MVarId) (target : Expr) : AscendM (Option MVarId) := do
  unless target.isAppOfArity ``Ascent.RTriple 22 do return none
  let [goal] ← goal.applyConst ``Ascent.RTriple.intro | return none
  return some (← preprocessMVar goal)

/-- Strategy: beta-reduce the right-hand side of the entailment; rebound couplings arrive as
`(fun av cv => …) v c` after a leaf consumes them. -/
private def rhsBeta? (goal : MVarId) (relHead : Expr) (relArgs : Array Expr) :
    AscendM (Option MVarId) := do
  let rhs := relArgs[3]!
  unless rhs.getAppFn.isLambda do return none
  let target ← shareCommonInc <|
    mkApp4 relHead relArgs[0]! relArgs[1]! relArgs[2]! rhs.headBeta
  return some (← goal.replaceTargetDefEq target)

/-- Strategy: beta-reduce the program head; continuations arrive as `c₂ cv`. -/
private def progBeta? (goal : MVarId) (g : RWPApp) : AscendM (Option MVarId) := do
  unless g.c.getAppFn.isLambda do return none
  let rhs := mkAppN g.head (g.args.set! 18 g.c.headBeta)
  let target ← shareCommonInc <| mkApp4 g.relHead g.relArgs[0]! g.relArgs[1]! g.pre rhs
  return some (← goal.replaceTargetDefEq target)

/-- Strategy: apply a registered spec for the program, most specific first. -/
private def applySpec (goal : MVarId) (g : RWPApp) : AscendM SolveResult := do
  let mut cands ← (← read).specs.getMatch g.c
  cands := cands.qsort fun s₁ s₂ => s₁.specificity > s₂.specificity
  for spec in cands do
    if let some ng ← applyRule goal g spec then
      return .goals [ng]
  return .stop (.noSpecFound g.c)

/-- Strategy: split a conjunction on the right, at the `Prop` lattice. The left conjunct is
instantiated (it is inspected downstream); the right conjunct carries the continuation and
stays untouched. -/
private def andSplit? (goal : MVarId) (relHead : Expr) (relArgs : Array Expr) :
    AscendM (Option (List MVarId)) := do
  let rhs := relArgs[3]!
  unless rhs.isAppOfArity ``And 2 do return none
  let pre := relArgs[2]!
  let A ← instantiateMVars rhs.getAppArgs[0]!
  let B := rhs.getAppArgs[1]!
  let ngA ← mkFreshExprSyntheticOpaqueMVar
    (← shareCommonInc (mkApp4 relHead relArgs[0]! relArgs[1]! pre A))
  let ngB ← mkFreshExprSyntheticOpaqueMVar
    (← shareCommonInc (mkApp4 relHead relArgs[0]! relArgs[1]! pre B))
  goal.assign (mkApp5 (mkConst ``Ascend.prop_le_and) pre A B ngA ngB)
  return some [ngA.mvarId!, ngB.mvarId!]

/-- Strategy: introduce an implication on the right, at the `Prop` lattice; the hypothesis
(a guard, or an established coupling) reaches the context through `forallIntro?`. -/
private def impIntro? (goal : MVarId) (relHead : Expr) (relArgs : Array Expr) :
    AscendM (Option MVarId) := do
  let rhs := relArgs[3]!
  unless rhs.isArrow do return none
  let pre := relArgs[2]!
  let A ← instantiateMVars rhs.bindingDomain!
  let B := rhs.bindingBody!
  let inner := mkApp4 relHead relArgs[0]! relArgs[1]! pre B
  let ng ← mkFreshExprSyntheticOpaqueMVar (← shareCommonInc (← mkArrow A inner))
  goal.assign (mkApp4 (mkConst ``Ascend.prop_le_imp) pre A B ng)
  return some ng.mvarId!

/-- Strategy: close a reflexive equation on the right. -/
private def eqRefl? (goal : MVarId) (relArgs : Array Expr) : AscendM (Option Unit) := do
  let rhs := relArgs[3]!
  unless rhs.isAppOfArity ``Eq 3 do return none
  let args ← rhs.getAppArgs.mapM (instantiateMVars ·)
  unless isSameExpr args[1]! args[2]! || args[1]! == args[2]! do return none
  let u ← Sym.getLevel args[0]!
  goal.assign (mkApp3 (mkConst ``Ascend.prop_le_eq_refl [u]) relArgs[2]! args[0]! args[1]!)
  return some ()

/-- Strategy: close against a hypothesis, such as a coupling established by an earlier leaf. -/
private def hypClose? (goal : MVarId) (relArgs : Array Expr) : AscendM (Option Unit) := do
  let rhs ← instantiateMVars relArgs[3]!
  -- Most recent first: the wanted coupling is typically the last leaf's.
  let decls := (← getLCtx).decls.toArray.filterMap id
  let mut found := none
  for i in [:decls.size] do
    let d := decls[decls.size - 1 - i]!
    unless d.isImplementationDetail do
      let ty ← instantiateMVars d.type
      if isSameExpr ty rhs || ty == rhs then
        found := some d
        break
  let some hyp := found | return none
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
  -- An assigned coupling slot arrives as `?Q v c`; substitute the head so beta reduction and
  -- the `rwp` parse below see the rebound continuation.
  let relArgs := relArgs.set! 3 (← instantiateMVarsIfMVarApp relArgs[3]!)
  if let some goal ← rhsBeta? goal relHead relArgs then return .goals [goal]
  if let some g := parseRWP? (mkApp4 relHead relArgs[0]! relArgs[1]! relArgs[2]! relArgs[3]!) then
    if let some goal ← progBeta? goal g then return .goals [goal]
    return ← applySpec goal g
  -- Rule application leaves assigned-but-unsubstituted metavariables (and levels) in the
  -- targets it builds; the strategies instantiate exactly what they inspect, never the
  -- continuation slot.
  if (← instantiateMVars relArgs[0]!).isProp then
    if let some goals ← andSplit? goal relHead relArgs then return .goals goals
    if let some goal ← impIntro? goal relHead relArgs then return .goals [goal]
    if let some _ ← eqRefl? goal relArgs then return .goals []
    if let some _ ← hypClose? goal relArgs then return .goals []
  return .stop (.noProgress relArgs[2]! relArgs[3]!)

end Ascend
