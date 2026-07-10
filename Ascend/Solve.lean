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

/-- Substitute an assigned metavariable at the application head only. This is the engine's
analogue of `instantiateMVarsIfMVarApp`: that helper instantiates the whole application, but a
rebound coupling's body carries the chain's synthesis metavariables, so the full instantiation
would walk the entire remaining chain at every handoff. The body's own assignments substitute
lazily when they reach a head position themselves. -/
private partial def instantiateHead (e : Expr) : MetaM Expr := do
  let .mvar id := e.getAppFn | return e
  let some val ← getExprMVarAssignment? id | return e
  instantiateHead (mkAppN val e.getAppArgs)

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
  let target := mkApp4 relHead relArgs[0]! relArgs[1]! relArgs[2]! rhs.headBeta
  return some (← setTargetRaw goal target)

/-- Strategy: beta-reduce the program head; continuations arrive as `c₂ cv`. -/
private def progBeta? (goal : MVarId) (g : RWPApp) : AscendM (Option MVarId) := do
  unless g.c.getAppFn.isLambda do return none
  let rhs := mkAppN g.head (g.args.set! 18 g.c.headBeta)
  let target := mkApp4 g.relHead g.relArgs[0]! g.relArgs[1]! g.pre rhs
  return some (← setTargetRaw goal target)

/-- Strategy: apply a registered spec for the program, most specific first. -/
private def applySpec (goal : MVarId) (g : RWPApp) : AscendM SolveResult := do
  -- A bind whose head matches a leaf spec applies as one fused rule per chain link.
  if g.c.isAppOfArity ``Bind.bind 6 then
    let mut heads ← (← read).specs.getMatch g.c.getAppArgs[4]!
    heads := heads.qsort fun s₁ s₂ => s₁.specificity > s₂.specificity
    for spec in heads do
      if let some ngs ← applyRule goal g spec (fuseBind := true) then
        return .goals ngs
  let mut cands ← (← read).specs.getMatch g.c
  cands := cands.qsort fun s₁ s₂ => s₁.specificity > s₂.specificity
  for spec in cands do
    if let some ngs ← applyRule goal g spec then
      return .goals ngs
  return .stop (.noSpecFound g.c)

/-- Strategy: close a reflexive equation on the right. The compared sides are substituted:
rule application binds by metavariable assignment, and comparison needs canonical forms. -/
private def eqRefl? (goal : MVarId) (relArgs : Array Expr) : AscendM (Option Unit) := do
  let rhs := relArgs[3]!
  unless rhs.isAppOfArity ``Eq 3 do return none
  let args ← rhs.getAppArgs.mapM (instantiateMVars ·)
  -- One-point: a flex side is a synthesis choice pinned by this very equation.
  if args[1]!.isMVar then
    unless ← isDefEq args[1]! args[2]! do return none
  else
    unless isSameExpr args[1]! args[2]! || args[1]! == args[2]! do return none
  let u ← Sym.getLevel args[0]!
  goal.assign (mkApp3 (mkConst ``Ascend.prop_le_eq_refl [u]) relArgs[2]! args[0]! args[1]!)
  return some ()

/-- Strategy: close against a hypothesis, such as a coupling established by an earlier leaf.
The compared propositions are substituted: comparison needs canonical forms. -/
private def hypClose? (goal : MVarId) (relArgs : Array Expr) : AscendM (Option Unit) := do
  let rhs ← instantiateMVars relArgs[3]!
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
  goal.assign (mkApp3 (mkConst ``Ascend.prop_le_of) relArgs[2]! rhs hyp.toExpr)
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
  let some (relHead, relArgs) := parseRel? target
    | return .stop (.noEntailment target)
  -- An assigned coupling slot arrives as `?Q v c`; substitute the head so beta reduction and
  -- the `rwp` parse below see the rebound continuation.
  let relArgs := relArgs.set! 3 (← instantiateHead relArgs[3]!)
  if let some goal ← rhsBeta? goal relHead relArgs then return .goals [goal]
  if let some g := parseRWP? (mkApp4 relHead relArgs[0]! relArgs[1]! relArgs[2]! relArgs[3]!) then
    if let some goal ← progBeta? goal g then return .goals [goal]
    return ← applySpec goal g
  -- The carrier arrives as `Sort ?u` with `?u` assigned, from rules applied at fresh levels.
  if ← isPropCarrier relArgs[0]! then
    if let some _ ← eqRefl? goal relArgs then return .goals []
    if let some _ ← hypClose? goal relArgs then return .goals []
  return .stop (.noProgress relArgs[2]! relArgs[3]!)

end Ascend
