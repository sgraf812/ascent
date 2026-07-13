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

/-- Strategy: expand an applied rebound-coupling combinator, `rwpCont γ a₂ c₂ Q E v c`, to
the continuation's `rwp`. The combinator form keeps rule-built goals lambda-free (a short
application spine with a constant prefix instead of ~30 fresh nodes per bind). -/
private def contExpand? (goal : MVarId) (target : Expr) : AscendM (Option MVarId) := do
  let_expr Lean.Order.PartialOrder.rel carrier inst pre rhs := target | return none
  unless rhs.getAppFn.isConstOf ``Ascent.rwpCont do return none
  let some rhs ← unfoldDefinition? rhs | return none
  return some (← setTargetRaw goal (mkApp4 target.getAppFn carrier inst pre rhs.headBeta))

/-- Strategy: beta-reduce the right-hand side of the entailment; rebound couplings arrive as
`(fun av cv => …) v c` after a leaf consumes them. -/
private def rhsBeta? (goal : MVarId) (target : Expr) : AscendM (Option MVarId) := do
  let_expr Lean.Order.PartialOrder.rel carrier inst pre rhs := target | return none
  unless rhs.getAppFn.isLambda do return none
  return some (← setTargetRaw goal (mkApp4 target.getAppFn carrier inst pre rhs.headBeta))

/-- Strategy: beta-reduce the program head; continuations arrive as `c₂ cv`. -/
private def progBeta? (goal : MVarId) (target : Expr) (g : RWPApp) : AscendM (Option MVarId) := do
  unless g.c.getAppFn.isLambda do return none
  let_expr Lean.Order.PartialOrder.rel carrier inst pre _ := target | return none
  let rhs := mkAppN g.head (g.args.set! 18 g.c.headBeta)
  return some (← setTargetRaw goal (mkApp4 target.getAppFn carrier inst pre rhs))

/-- Strategy: apply a registered spec for the program, most specific first. -/
private def applySpec (goal : MVarId) (g : RWPApp) : AscendM SolveResult := do
  let mut cands ← (← read).specs.getMatch g.c
  cands := cands.qsort fun s₁ s₂ => s₁.specificity > s₂.specificity
  for spec in cands do
    if let some ngs ← applyRule goal g spec then
      return .goals ngs
  return .stop (.noSpecFound g.c)

/-- Strategy: close a reflexive equation on the right. The compared sides are substituted:
rule application binds by metavariable assignment, and comparison needs canonical forms. -/
private def eqRefl? (goal : MVarId) (target : Expr) : AscendM (Option Unit) := do
  let_expr Lean.Order.PartialOrder.rel _ _ pre rhs := target | return none
  unless rhs.isAppOfArity ``Eq 3 do return none
  let args ← rhs.getAppArgs.mapM (instantiateMVars ·)
  -- One-point: a flex side is a synthesis choice pinned by this very equation.
  if args[1]!.isMVar then
    unless ← isDefEq args[1]! args[2]! do return none
  else
    unless isSameExpr args[1]! args[2]! || args[1]! == args[2]! do return none
  let u ← Sym.getLevel args[0]!
  goal.assign (mkApp3 (mkConst ``Ascend.prop_le_eq_refl [u]) pre args[0]! args[1]!)
  return some ()

/-- Strategy: close against a hypothesis, such as a coupling established by an earlier leaf.
The compared propositions are substituted: comparison needs canonical forms. -/
private def hypClose? (goal : MVarId) (target : Expr) : AscendM (Option Unit) := do
  let_expr Lean.Order.PartialOrder.rel _ _ pre rhsRaw := target | return none
  let rhs ← instantiateMVars rhsRaw
  -- Most recent first, without materializing the context: the wanted coupling is typically
  -- the last leaf's, the immediately preceding declaration.
  let decls := (← getLCtx).decls
  let mut found := none
  for i in [:decls.size] do
    if let some (some d) := decls[decls.size - 1 - i]? then
      unless d.isImplementationDetail do
        let ty ← instantiateMVars d.type
        if isSameExpr ty rhs || ty == rhs then
          found := some d
          break
  let some hyp := found | return none
  goal.assign (mkApp3 (mkConst ``Ascend.prop_le_of) pre rhs hyp.toExpr)
  return some ()

/-- Whether the entailment carrier is `Prop`, seeing through an assigned level. -/
private def isPropCarrier (carrier : Expr) : MetaM Bool := do
  let .sort u := carrier | return false
  return (← instantiateLevelMVars u).isZero

/--
One solve step, dispatching the strategies in order: introduce `∀`/implication targets, unfold
an `RTriple` target, then on `pre ⊑ rhs` beta-reduce the right-hand side, decompose an `rwp`
application through the registered specs, and close residual `Prop`-lattice entailments (spec
preconditions arrive already curried into subgoals by rule compilation).
-/
def solve (goal : MVarId) : AscendM SolveResult := goal.withContext do
  let target ← goal.getType
  if let some goal ← forallIntro? goal target then return .goals [goal]
  if let some goal ← rtripleIntro? goal target then return .goals [goal]
  let_expr Lean.Order.PartialOrder.rel carrier inst pre rhs := target
    | return .stop (.noEntailment target)
  -- An assigned coupling slot arrives as `?Q v c`; substitute the head so beta reduction and
  -- the `rwp` parse below see the rebound continuation. Refresh the entailment with it.
  let rhs ← instantiateMVarsIfMVarAppS rhs
  let target := mkApp4 target.getAppFn carrier inst pre rhs
  if let some goal ← contExpand? goal target then return .goals [goal]
  if let some goal ← rhsBeta? goal target then return .goals [goal]
  if let some g := parseRWP? rhs then
    if let some goal ← progBeta? goal target g then return .goals [goal]
    return ← applySpec goal g
  -- The carrier arrives as `Sort ?u` with `?u` assigned, from rules applied at fresh levels.
  if ← isPropCarrier carrier then
    if let some _ ← eqRefl? goal target then return .goals []
    if let some _ ← hypClose? goal target then return .goals []
  return .stop (.noProgress pre rhs)

end Ascend
