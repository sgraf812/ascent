import Ascend.Normalize

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
  /-- The goal was decomposed into these subgoals, sharing `scope`. -/
  | goals (scope : Scope) (subgoals : List MVarId)
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

/-- Reshape strategy: expand an applied rebound-coupling combinator, `rwpCont γ a₂ c₂ Q E v c`,
to the continuation's `rwp`. The combinator form keeps rule-built goals lambda-free (a short
application spine with a constant prefix instead of ~30 fresh nodes per bind). -/
private def contExpand? (rhs : Expr) : AscendM (Option Expr) := do
  unless rhs.getAppFn.isConstOf ``Ascent.rwpCont do return none
  let some rhs ← unfoldDefinition? rhs | return none
  return some rhs.headBeta

/-- Reshape strategy: beta-reduce the entailment's right-hand side; rebound couplings arrive as
`(fun av cv => …) v c` after a leaf consumes them. -/
private def rhsBeta? (rhs : Expr) : Option Expr :=
  if rhs.getAppFn.isLambda then some rhs.headBeta else none

/-- Reshape strategy: activate a pending sub-program hole. The abstract slot is headed by a
let-bound fvar (introduced at rule application for a postponed sub-program); zeta-expand this one
occurrence so the slot exposes the underlying web metavariable and becomes the active slot. -/
private def holeZeta? (g : RWPApp) : AscendM (Option Expr) := do
  let some fvarId := g.a.getAppFn.fvarId? | return none
  let some val ← fvarId.getValue? | return none
  return some (g.withA (mkAppN val g.a.getAppArgs))

/-- Reshape strategy: beta-reduce the program head; continuations arrive as `c₂ cv`. -/
private def progBeta? (g : RWPApp) : Option Expr :=
  if g.c.getAppFn.isLambda then some (g.withC g.c.headBeta) else none

/-- Strategy: apply a registered spec for the program, most specific first. -/
private def applySpec (scope : Scope) (goal : MVarId) (g : RWPApp) : AscendM SolveResult := do
  let mut cands ← (← read).specs.getMatch g.c
  cands := cands.qsort fun s₁ s₂ => s₁.specificity > s₂.specificity
  for spec in cands do
    if let some ngs ← applyRule goal g spec then
      return .goals scope ngs
  return .stop (.noSpecFound g.c)

/--
One solve step. Shape the target to `pre ⊑ rhs` (introduce `∀` targets, unfold an `RTriple`),
reshape the right-hand side (unfold a rebound coupling, beta-reduce), close reflexively, drive the
precondition toward `⊤` lifting pure content into the context, decompose a lattice connective
through the reused split rules, discharge a residual `⌜φ⌝` against the last lifted hypothesis, and
otherwise decompose the `rwp` application through the registered specs.
-/
def solve (scope : Scope) (goal : MVarId) : AscendM SolveResult := goal.withContext do
  let target ← goal.getType
  if let some goal ← forallIntro? goal target then return .goals scope [goal]
  if let some goal ← rtripleIntro? goal target then return .goals scope [goal]
  if let some _ ← liftedHypBare? scope goal target then return .goals scope []
  let_expr rel@Lean.Order.PartialOrder.rel carrier inst pre rhs := target
    | return .stop (.noEntailment target)
  -- Rebuild the entailment with a reshaped right-hand side; the four reshapers only compute the
  -- new `rhs`, so the destructure and `mkApp4` rebuild happen once, here.
  let reshape (rhs' : Expr) : AscendM SolveResult := do
    return .goals scope [← setTargetRaw goal (mkApp4 rel carrier inst pre rhs')]
  if let some rhs' ← contExpand? rhs then return ← reshape rhs'
  if let some rhs' := rhsBeta? rhs then return ← reshape rhs'
  if let some gs ← rfl? goal then return .goals scope gs
  if let some (scope, gs) ← normalizePre? scope goal carrier pre target then return .goals scope gs
  if let some gs ← splitLatticeOp? goal rhs then return .goals scope gs
  if let some _ ← liftedHyp? scope goal carrier pre rhs then return .goals scope []
  if let some g := parseRWP? rhs then
    if let some rhs' ← holeZeta? g then return ← reshape rhs'
    if let some rhs' := progBeta? g then return ← reshape rhs'
    return ← applySpec scope goal g
  return .stop (.noProgress pre rhs)

end Ascend
