/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/

import Ascent.Tactic.VCGen.Shim
import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.RuleCache
import Ascent.Tactic.VCGen.RuleCache
import Lean.Elab.Tactic.VCGen.Entails
import Lean.Elab.Tactic.VCGen.JoinPoint
import Ascent.Tactic.VCGen.JoinPoint
import Lean.Elab.Tactic.VCGen.BinderName
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.Simp.App
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.LitValues
import Lean.Meta.Sym.InstantiateMVarsS

open Lean Meta Elab Tactic Sym Sym.Internal
open Lean.Elab.Tactic.VCGen.SpecAttr
open Lean.Elab.Tactic.VCGen
open Std.WP Lean.Order

namespace Lean.Elab.Tactic.VCGen.Ascend

/-!
The main `solve` step. Runs once per worklist iteration and either fully
decomposes the current goal into subgoals, or reports why no further
progress is possible (`SolveResult`).
-/


/-- The reason why no further VC generation progress is possible on the current goal. -/
inductive SolveResult.StopReason where
  /-- Out of fuel. -/
  | outOfFuel
  /-- `until <pat>` matched. -/
  | untilPatternMatched (m : Expr)
  /-- The target was not of the form `pre ⊑ rhs`. -/
  | noEntailment (target : Expr)
  /-- The target was of the form `pre ⊑ rhs`, but we couldn't make further progress. -/
  | noProgress (pre rhs : Expr)
  /-- No spec applicable to the program `e` in `pre ⊑ wp e post eposts s₁ ... sₙ` was found; `thms`
  are the candidates that were tried. Reached only when `errorOnMissingSpec` is `false`. -/
  | noSpecFound (e : Expr) (monad : Expr) (thms : Array SpecTheorem)

/-- The result of one `solve` step of VC generation. -/
inductive SolveResult where
  /-- Successfully decomposed the goal. These are the subgoals, sharing `scope`. -/
  | goals (scope : Scope) (subgoals : List MVarId)
  /-- No further progress possible; emit the current goal as a VC. -/
  | stop (reason : SolveResult.StopReason)

def isDuplicable (e : Expr) : Bool := match e with
  | .bvar .. | .mvar .. | .fvar .. | .const .. | .lit .. | .sort .. => true
  | .mdata _ e | .proj _ _ e => isDuplicable e
  | .lam .. | .forallE .. | .letE .. => false
  | .app .. => e.isAppOf ``OfNat.ofNat || (Sym.getBitVecValue? e).run.isSome
    || (Sym.getCharValue? e).run.isSome

/-- Strip an annotation, such as the `noImplicitLambda` metadata a tactic `have`/`let`/`suffices`
leaves on the goal, so later strategies and the backward rules they invoke see the bare target. -/
def consumeMData? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  unless target.isMData do return none
  return some (← goal.replaceTargetDefEqFast target.consumeMData)

/-- Apply the backward rule `rule` of a `@[vcgen_rintro]` rule to `goal`. The types of the new goals
are instantiated, so that the rule parameter `G` is beta-reduced at its arguments. -/
def applyRIntroRule (goal : MVarId) (rule : BackwardRule) : VCGenM (Option (List MVarId)) := do
  let .goals gs ← rule.apply goal | return none
  some <$> gs.mapM fun g => do
    let ty ← g.getType
    let ty' ← instantiateMVarsS ty
    if isSameExpr ty ty' then return g
    g.replaceTargetDefEqFast ty'

/-- Strategy 1a: apply the first of the `@[vcgen_rintro]` rules `entries`, in priority order, that
applies to the target of `goal`. -/
def applyRIntroRules (goal : MVarId) (entries : Array RIntroEntry) :
    VCGenM (Option (List MVarId)) := do
  for entry in entries.insertionSort (·.prio > ·.prio) do
    if let some gs ← applyRIntroRule goal (← mkBackwardRuleForRIntroCached entry) then
      trace[Elab.Tactic.Do.vcgen] "Applied rintro rule {entry.declName}"
      return some gs
    trace[Elab.Tactic.Do.vcgen] "Rintro rule {entry.declName} does not apply"
  return none

/-- Strategy 1: simp the target, then introduce its binders. One pass over the binders matches each
`∀` binder against the `@[vcgen_rintro]` rules once. A matching rule destructures the binder, and
the binders between two matches are introduced at once. -/
def forallIntro? (oldGoal : MVarId) (target : Expr) : VCGenM (Option (List MVarId)) := do
  unless target.isForall do return none
  let oldGoal ← instantiateBinderDomains oldGoal
  let mut goal ← match ← simpGoalTelescope oldGoal with
    | .closed => return some []
    | .goal goal => pure goal
    | .noProgress => pure oldGoal
  let rintros := (← read).rintros
  let mut e ← goal.getType
  let mut n := 0
  repeat
    match e with
    | .forallE _ _ b _ =>
      let entries := Sym.getMatch (← getMCtx) rintros e
      unless entries.isEmpty do
        goal ← introsHygienicN goal n
        n := 0
        if let some gs ← applyRIntroRules goal entries then return some gs
      n := n + 1
      e := b
    | .letE _ _ _ b _ =>
      n := n + 1
      e := b
    | _ => break
  goal ← introsHygienicN goal n
  if goal == oldGoal then
    throwError "Failed to intro forall target {goal}"
  return some [goal]

/-- Strategy 2: zeta-substitute a duplicable top-level `let` in the target, otherwise
introduce it into the local context. -/
def targetLetIntro? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let .letE name _ val body _ := target | return none
  if isDuplicable val then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {name}"
    return some (← goal.replaceTargetDefEqFast (← Sym.instantiateRevBetaS body #[val]))
  else
    trace[Elab.Tactic.Do.vcgen] "let-intro: {name}"
    return some (← introsHygienic goal)

/-- Strategy 3: unfold a `Triple` target into the underlying lattice entailment. -/
def tripleUnfold? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  unless target.isAppOf ``Ascent.Refinement do return none
  return some (← unfoldRefinement goal)

/-- Strategy 3b: turn a bare `wp` application target (a `Prop`) into `⊤ ⊑ wp …`. Entry-point
goals produced by the `of_run_eq_wp` lemmas have this shape. -/
def bareWPToLe? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let some _ := isWRPApp? target | return none
  let newTarget ← mkAppM ``PartialOrder.rel #[← mkAppOptM ``Lean.Order.top #[mkSort 0, none], target]
  let newTarget ← shareCommon newTarget
  let g ← liftMetaM <| mkFreshExprSyntheticOpaqueMVar newTarget
  goal.assign (mkApp2 (mkConst ``Lean.Order.of_top_le_prop) target g)
  return some g.mvarId!

/-- Strategy 4: close a reflexive entailment `pre ⊑ pre` by applying `PartialOrder.rel_refl`.
Runs before the precondition lift so a spec handoff `pre ⊑ specPre` closes by unification rather
than an assumption search. The pattern matcher keeps synthetic-opaque invariant holes rigid, so
`⊤ ⊑ ?inv args` is left untouched. -/
def rfl? (goal : MVarId) : VCGenM (Option (List MVarId)) := do
  let .goals gs ← (← read).backwardRules.refl.apply goal | return none
  trace[Elab.Tactic.Do.vcgen] "Solved by rfl {goal}"
  return some gs

/-- The most recently lifted pure precondition (cached in `Scope.lastLiftedPre?`) whose type is
the same hash-consed expression as `e`, or `none`. Must run in `goal`'s context. -/
def liftedPreFor? (scope : Scope) (e : Expr) : VCGenM (Option LocalDecl) := do
  let some fvarId := scope.lastLiftedPre? | return none
  let some hyp := (← getLCtx).find? fvarId | return none
  unless isSameExpr e hyp.type do return none
  trace[Elab.Tactic.Do.vcgen] "Solved by lifted hypothesis {hyp.userName}"
  return some hyp

/-- Strategy 10: close `pre ⊑ φ` on the `Prop` lattice against the most recently lifted pure
precondition. Runs after lattice decomposition, so `φ` is an opaque proposition rather than a
lattice connective. This is one comparison against one hypothesis, not an assumption search. -/
def liftedHyp? (scope : Scope) (goal : MVarId) (α pre rhs : Expr) :
    VCGenM (Option (List MVarId)) :=
  goal.withContext do
    unless α.isProp do return none
    let some hyp ← liftedPreFor? scope rhs | return none
    goal.assign (← mkAppM ``Lean.Order.le_prop_of_right #[pre, rhs, hyp.toExpr])
    return some []

/-- Close a bare `Prop` residual, such as the subgoal of the `⌜φ⌝` lattice rule, against the
most recently lifted pure precondition. Runs when the target is not a lattice entailment,
just before it would be classified as a VC. -/
def liftedHypBare? (scope : Scope) (goal : MVarId) (target : Expr) :
    VCGenM (Option (List MVarId)) :=
  goal.withContext do
    let some hyp ← liftedPreFor? scope target | return none
    goal.assign hyp.toExpr
    return some []

/-- Replace the `i`-th argument of the application `e`, which has `n` arguments. -/
def setAppArg (e : Expr) (i n : Nat) (v : Expr) : Expr :=
  match e with
  | .app f a => if n == i + 1 then e.updateApp! f v else e.updateApp! (setAppArg f i (n-1) v) a
  | _ => e

/-- Instantiate an assigned metavariable in the program of the `wp` application `rhs`. -/
def instantiateWPProg? (rhs : Expr) : VCGenM (Option Expr) := do
  unless rhs.hasMVar do return none
  let n := rhs.getAppNumArgs
  unless n > 7 && rhs.getAppFn.isConstOf ``Std.WP.wp do return none
  let prog := rhs.getArg! WRPApp.progIdx n
  let prog' ← instantiateMVarsIfMVarAppS prog
  if isSameExpr prog prog' then return none
  return some (← shareCommon (setAppArg rhs WRPApp.progIdx n prog'))

/-- Instantiate assigned head metavariables in the goal's entailment, so the shape tests in the
following steps see the assigned form. -/
def instantiateGoal? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let_expr c@PartialOrder.rel α inst pre rhs := target | return none
  let α' ← reduceHead α
  let pre' ← reduceHead pre
  let rhs' ← reduceHead rhs
  let rhs' := (← instantiateWPProg? rhs').getD rhs'
  if isSameExpr α α' && isSameExpr pre pre' && isSameExpr rhs rhs' then return none
  return some (← goal.replaceTargetDefEqFast (← mkAppNS c #[α', inst, pre', rhs']))

/-- Strategy 5: cancel a redundant `P ⊓ ⊤` precondition via `meet_top_le_of_le`, leaving `P ⊑ rhs`.
Such a precondition arises when `himp_complete` splits `⊤ ⊑ a ⇨ b` into `a ⊓ ⊤ ⊑ b`. -/
def stripMeetTopPre? (goal : MVarId) (pre : Expr) : VCGenM (Option MVarId) := do
  let_expr Lean.Order.meet _l _inst _P top := pre | return none
  unless top.isAppOf ``Lean.Order.top do return none
  let .goals [g] ← (← read).backwardRules.meetTop.applyChecked goal
    | throwError "Failed to cancel the `⊓ ⊤` precondition of {goal}"
  return some g

/-- Strategy 5: lift an embedded pure precondition `⌜φ⌝` into the local context, leaving `⊤`
as the residual precondition. Runs before state-argument introduction, which would otherwise
leave `⌜φ⌝` applied to the introduced arguments. Returns the new goal and the hypothesis, if any. -/
def ofPropPreIntro? (goal : MVarId) (pre : Expr) : VCGenM (Option (MVarId × Option FVarId)) := do
  let_expr CompleteLattice.ofProp _l _inst φ := pre | return none
  if φ.isTrue then return none
  return some (← introPre (← read).backwardRules.ofPropPreIntro goal)

/-- Strategy 5: lift the pure `φ` of a `⌜φ⌝ ⊓ P` precondition into the local context, leaving
`P ⊑ rhs`. -/
def ofPropMeetPreIntro? (goal : MVarId) (pre : Expr) : VCGenM (Option (MVarId × Option FVarId)) := do
  let_expr Lean.Order.meet _l _inst lhs _rest := pre | return none
  let_expr CompleteLattice.ofProp _l' _inst' _φ := lhs | return none
  return some (← introPre (← read).backwardRules.ofPropMeetPreIntro goal)

/-- Strategy 5: eliminate an `iSup` precondition via `iSup_le`, leaving the pointwise entailment
`∀ i, P i ⊑ rhs` for `∀`-introduction. -/
def iSupPreIntro? (goal : MVarId) (pre : Expr) : VCGenM (Option MVarId) := do
  unless pre.isAppOfArity ``Lean.Order.iSup 4 do return none
  let .goals [g] ← (← read).backwardRules.iSupPreIntro.applyChecked goal
    | throwError "Failed to eliminate the `iSup` precondition of {goal}"
  return some g

/-- Strategy 7: move a bare `Prop` precondition `φ ⊑ rhs` into the local context via
`le_of_imp_top_le`, leaving `⊤ ⊑ rhs`. Runs after `True` and `⊤` preconditions are handled, so
`φ` carries information worth keeping. Returns the new goal and the introduced hypothesis, if any. -/
def barePreIntro? (goal : MVarId) (α pre : Expr) : VCGenM (Option (MVarId × Option FVarId)) := do
  unless α.isProp do return none
  if pre.isAppOf ``Lean.Order.top then return none
  return some (← introPre (← read).backwardRules.propPreIntro goal)

/-- Strategy 7: replace a `True` precondition by `⊤` via `true_le_of_top_le`, or reduce a lifted
`⊤ s₁ … sₙ` precondition (the bare top applied to the state arguments introduced by
`le_of_forall_le`) to the bare `⊤` via a `top_apply` rewrite. Either way the goal follows the `⊤`
path instead of lifting into the local context, and a `⊤`-precondition VC reaches `elimTopPre` in the
bare form that `top_le_prop` can strip. -/
def normalizePreToTop? (goal : MVarId) (pre target : Expr) : VCGenM (Option (List MVarId)) := do
  if pre.isTrue then
    let .goals [g] ← (← read).backwardRules.truePreIntro.applyChecked goal
      | throwError "Failed to apply {.ofConstName ``Lean.Order.true_le_of_top_le} to{indentExpr target}"
    return some [g]
  if let some g ← reduceTopAppliedPre? goal target pre then
    return some [g]
  return none

/-- Phase 2: drive the precondition of `pre ⊑ rhs` toward `⊤`, lifting any pure content into the
local context so a later spec application sees a `⊤` precondition. In order: cancel a redundant
`⊓ ⊤`; lift an embedded `⌜φ⌝` (before state-argument introduction, which would otherwise leave
`⌜φ⌝` applied to the introduced state); lift the guard of a `⌜φ⌝ ⊓ P`; eliminate an `iSup`;
introduce excess state arguments; drop a `True` precondition; lift a bare `Prop` precondition.
Returns the updated scope, recording any lifted hypothesis. -/
def normalizePre? (scope : Scope) (goal : MVarId) (α pre target : Expr) :
    VCGenM (Option (Scope × List MVarId)) := do
  if let some g ← stripMeetTopPre? goal pre then
    return some (scope, [g])
  if let some (g, h) ← ofPropPreIntro? goal pre then
    return some ({ scope with lastLiftedPre? := h <|> scope.lastLiftedPre? }, [g])
  if let some (g, h) ← ofPropMeetPreIntro? goal pre then
    return some ({ scope with lastLiftedPre? := h <|> scope.lastLiftedPre? }, [g])
  if let some g ← iSupPreIntro? goal pre then
    return some (scope, [g])
  if let some goal' ← introsExcessArgs goal then return some (scope, [goal'])
  if let some gs ← normalizePreToTop? goal pre target then
    return some (scope, gs)
  if let some (g, h) ← barePreIntro? goal α pre then
    return some ({ scope with lastLiftedPre? := h <|> scope.lastLiftedPre? }, [g])
  return none

/-- Replace the right-hand side of the entailment in `goal`'s target with `rhs` (which must be
definitionally equal). -/
def replaceRhsDefEq (goal : MVarId) (rhs : Expr) : VCGenM MVarId := do
  let target ← goal.getType
  let relArgs := target.getAppArgs
  goal.replaceTargetDefEqFast (← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) rhs))

/-- Replace the program in `goal`'s target with `prog` (which must be definitionally equal). -/
def replaceProgDefEq (goal : MVarId) (info : WRPApp) (prog : Expr) :
    VCGenM MVarId := do
  let wp ← mkAppNS info.head <| info.args.set! WRPApp.progIdx prog
  replaceRhsDefEq goal (← mkAppNS wp info.excessArgs)

/-- Put `let name : type := val; body` in front of the entailment in `goal`'s target, where `body` is
the new right-hand side of the entailment, and introduce it as a local definition. -/
def introLet (goal : MVarId) (name : Name) (type val body : Expr) (nondep : Bool) :
    VCGenM (FVarId × MVarId) := do
  trace[Elab.Tactic.Do.vcgen] "let-intro: {name}"
  let target ← goal.getType
  let relArgs := target.getAppArgs
  let target ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) body)
  let goal ← goal.replaceTargetDefEqFast (.letE name type val target nondep)
  let name ← if isProgramName name then pure name else Meta.mkFreshBinderNameForTactic name
  let .goal decls goal' ← Sym.intros goal #[name]
    | throwError "Failed to intro the `let` {name}"
  return (decls[0]!, goal')

/-- Simplify the value `val` of `goal`'s target `pre ⊑ have name : type := val; body` with
`Context.simpMethods`. Returns the new goal and the simplified value. The value of a dependent `let`
(`nondep = false`) stays as written, since `body` can depend on it definitionally. -/
def simpHaveValue (goal : MVarId) (name : Name) (type val body : Expr) (nondep : Bool) :
    VCGenM (MVarId × Expr) := do
  unless nondep do return (goal, val)
  let some methods := (← read).simpMethods | return (goal, val)
  let .step val' h .. ← runSimp methods (Sym.Simp.simp val) | return (goal, val)
  let target ← goal.getType
  let relArgs := target.getAppArgs
  let rel ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) body)
  let target' ← mkAppNS target.getAppFn
    (relArgs.set! (relArgs.size - 1) (← mkHaveS name type val' body))
  let u ← Sym.getLevel type
  let h := mkApp6 (mkConst ``have_val_congr' [u, 1]) type (mkSort 0) val val' (.lam name type rel .default) h
  let .goal goal ← (Sym.Simp.Result.step target' h).toSimpGoalResult goal | return (goal, val)
  return (goal, val')

/-- Strip an `mdata` wrapper (such as the `save_info` annotation left by spec elaboration)
from the program in `goal`'s target, so the remaining strategies see the bare term. -/
def wpConsumeMData? (goal : MVarId) (info : WRPApp) : VCGenM (Option MVarId) := do
  let .mdata .. := info.prog | return none
  return some (← replaceProgDefEq goal info info.prog.consumeMData)

def wpReduceHead? (goal : MVarId) (info : WRPApp) : VCGenM (Option MVarId) := do
  let some prog ← reduceHead? info.prog | return none
  return some (← replaceProgDefEq goal info prog)

/-- Strategy 11a: introduce or zeta-substitute a `let` from the program head. Under `+jp`, an
introduced join point is registered, which adds the goal for its RHS. -/
def wpLet? (scope : Scope) (goal : MVarId) (info : WRPApp) :
    VCGenM (Option (Scope × List MVarId)) := do
  let .letE name type val body nondep := info.prog.getAppFn | return none
  let appArgs := info.prog.getAppRevArgs
  let val ← reduceHead val
  if isDuplicable val then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {name}"
    let body' ← Sym.instantiateRevBetaS body #[val]
    return some (scope, [← replaceProgDefEq goal info (← mkAppRevS body' appArgs)])
  let wp ← mkAppNS info.head <| info.args.set! WRPApp.progIdx (← mkAppRevS body appArgs)
  let (jp, goal) ← introLet goal name type val (← mkAppNS wp info.excessArgs) nondep
  if appArgs.isEmpty then
    if let some r ← registerJoinPoint scope goal jp val info then
      return some r
  return some (scope, [goal])

/-- Strategy 6: substitute or introduce a `let` or `have` at the head of the right-hand side of
`pre ⊑ rhs`. A spec precondition `fun s => have v := e s; P v s` gives such a right-hand side. The
value of a `have` is simplified first. -/
def rhsLet? (goal : MVarId) (rhs : Expr) : VCGenM (Option MVarId) := do
  let .letE name type val body nondep := rhs | return none
  let (goal, val) ← simpHaveValue goal name type (← reduceHead val) body nondep
  if isDuplicable val then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {name}"
    return some (← replaceRhsDefEq goal (← Sym.instantiateRevBetaS body #[val]))
  return some (← introLet goal name type val body nondep).2

/-- Strategy 11b: fold the state arguments of the program's `wp` application, so the symbolic
state a spec application threads through the goal is normalized as it is produced rather than left
to the discharging tactic. Rewrites with `Context.simpMethods`; the program, the postcondition and
the precondition are left untouched. -/
def wpSimpStateArgs? (goal : MVarId) (info : WRPApp) :
    VCGenM (Option (List MVarId)) := goal.withContext do
  if info.excessArgs.isEmpty then return none
  let some methods := (← read).simpMethods | return none
  let start := info.args.size
  let target ← goal.getType
  match h : target with
  | .app f rhs =>
    let result ← runSimp methods do
      let ar ← Sym.Simp.simpAppArgRange rhs start (start + info.excessArgs.size)
      Sym.Simp.mkCongr target f rhs .rfl ar h
    match ← result.toSimpGoalResult goal with
    | .closed => return some []
    | .goal g => return some [g]
    | .noProgress => return none
  | _ => return none

/-- The argument `x` of a hole as seen by `fillAbstractHole`: a free variable stays an argument, a
closed term of a subsingleton type (`Unit`, `PUnit`, a proof) is dropped, and a structure
instance whose fields are free variables contributes its fields. -/
inductive HoleArg where
  | keep (x : Expr)
  | drop
  /-- The projection functions of the structure, applied to its parameters, and the fields. -/
  | fields (projs : Array Expr) (xs : Array Expr)

def classifyHoleArg (x : Expr) : SymM (Option HoleArg) := do
  if x.isFVar then return some (.keep x)
  if !x.hasFVar && !x.hasMVar then
    let ty ← Sym.inferType x
    if ty.isConstOf ``Unit || ty.isAppOf ``PUnit || (← Sym.inferType ty).isProp then
      return some .drop
    return none
  let .const ctor us := x.getAppFn | return none
  let env ← getEnv
  let some (.ctorInfo cv) := env.find? ctor | return none
  let some info := getStructureInfo? env cv.induct | return none
  let ps := x.getAppArgs.extract 0 cv.numParams
  let fs := x.getAppArgs.extract cv.numParams x.getAppNumArgs
  unless fs.size == cv.numFields && fs.all (·.isFVar) && ps.all (!·.hasFVar) do return none
  let mut projs := #[]
  for f in info.fieldNames do
    let some p := getProjFnForField? env cv.induct f | return none
    projs := projs.push (mkAppN (.const p us) ps)
  return some (.fields projs fs)

/-- Rewrite the hole `?h xs` whose arguments `classifyHoleArg` accepts into `?h' ys`, applied to
the distinct free variables `ys` of `xs`: `?h := fun x₁ … xₙ => ?h' ys'`, where `ys'` reads each
variable off its argument (the argument itself, or a projection of a structure argument). The type
of `?h` must not depend on its arguments. Returns `?h'` and `ys`. -/
def patternHole? (hole : MVarId) (xs : Array Expr) : VCGenM (Option (Expr × Array Expr)) := do
  let mut cls := #[]
  for x in xs do
    let some c ← classifyHoleArg x | return none
    cls := cls.push c
  let ys := cls.foldl (init := #[]) fun acc c => match c with
    | .keep x => acc.push x
    | .drop => acc
    | .fields _ fs => acc ++ fs
  unless (ys.toList.map (·.fvarId!)).eraseDups.length == ys.size do return none
  let decl ← hole.getDecl
  let mut ty ← instantiateMVars decl.type
  let mut doms := #[]
  for _ in [0:xs.size] do
    let .forallE nm d body _ := ty | return none
    doms := doms.push (nm, d)
    ty := body
  if ty.hasLooseBVars || doms.any (·.2.hasLooseBVars) then return none
  let mut yTys := #[]
  for y in ys do
    let yTy ← instantiateMVars (← Sym.inferType y)
    if yTy.hasFVar || yTy.hasMVar then return none
    yTys := yTys.push yTy
  let ty' := (ys.zip yTys).foldr (fun (y, yTy) acc => .forallE `y yTy acc .default) ty
  let h' ← mkFreshExprMVarAt decl.lctx decl.localInstances ty'
  let n := xs.size
  let mut body := #[]
  for i in [0:n], c in cls do
    match c with
    | .keep _ => body := body.push (.bvar (n - 1 - i))
    | .drop => pure ()
    | .fields projs _ => for p in projs do body := body.push (.app p (.bvar (n - 1 - i)))
  hole.assign <| doms.foldr (fun (nm, d) acc => .lam nm d acc .default) (mkAppN h' body)
  return some (h', ys)

/-- Fill an unassigned hole in the abstract program of `goal` with a fresh metavariable `?b` of the
goal's context, which a rule then assigns. A bare hole is assigned `?b`. A hole `?h xs` applied to
distinct free variables gets the delayed assignment `?h xs := ?b`. A hole applied to closed terms,
such as the continuation `?k ()` of a bind whose first action returns `()`, is assigned the
constant function `fun _ => ?b`. A hole whose spine mixes free variables, closed terms of a
subsingleton type and structure instances of free variables, such as `?f () a` or `?f (a, b)`, is
solved through the partial inverse of its spine, as in nested pattern unification (Kovács and
Bocquet, WITS 2023): `(a, b)` inverts to the projections of the bound argument, and a closed
subsingleton argument inverts to nothing. The result is a hole `?h'` applied to the free variables
(`patternHole?`), which gets the delayed assignment. A table slot `Table.get ?tbl k` at a closed key gets the cell of `k` (`tableCell`). In
every case the goal's abstract program becomes the cell. The frontend resolves the delayed
assignments after the run. Returns the new goal and, for a filled hole, the hole's declaration,
the hole's arguments and `?b`. -/
def fillAbstractHole (goal : MVarId) (info : WRPApp) :
    VCGenM (MVarId × Option (MetavarDecl × Array Expr × Expr)) := do
  let mut goal := goal
  let mut filled : Option (MetavarDecl × Array Expr × Expr) := none
  let abs ← instantiateMVarsIfMVarAppS info.abs
  if abs.isAppOfArity ``Ascent.Table.get 6 then
    if let some (decl?, b) ← tableCell abs then
      if let some decl := decl? then filled := some (decl, #[], b)
      goal ← setAbs goal info b
  else if let .mvar hole := abs.getAppFn then
    let xs := abs.getAppArgs
    let distinct := xs.all (·.isFVar) && (xs.toList.map (·.fvarId!)).eraseDups.length == xs.size
    let closed := xs.all fun x => !x.hasFVar && !x.hasMVar
    if (← hole.getKind) matches .natural && !(← hole.isDelayedAssigned) && (distinct || closed) then
      let b ← shareCommon (← mkFreshExprMVar (← Sym.inferType abs))
      filled := some (← hole.getDecl, if closed then #[] else xs, b)
      if xs.isEmpty then
        hole.assign b
      else if closed then
        let mut ty ← instantiateMVars (← hole.getType)
        let mut doms := #[]
        for _ in [0:xs.size] do
          let .forallE nm d body _ := ty
            | throwError "ascend: the hole {mkMVar hole} applied to {xs} has no function type"
          doms := doms.push (nm, d)
          ty := body
        hole.assign <| doms.foldr (fun (nm, d) acc => .lam nm d acc .default) b
      else
        assignDelayedMVar hole xs b.mvarId!
        goal ← setAbs goal info b
    else if (← hole.getKind) matches .natural && !(← hole.isDelayedAssigned) then
      if let some (h', ys) ← patternHole? hole xs then
        let b ← shareCommon (← mkFreshExprMVar (← Sym.inferType abs))
        filled := some (← h'.mvarId!.getDecl, ys, b)
        assignDelayedMVar h'.mvarId! ys b.mvarId!
        goal ← setAbs goal info b
  return (goal, filled)

/-- `true` iff the abstract program of the filled hole `filled` uses only the hole's context and the
hole's arguments. -/
def filledInScope (filled : Option (MetavarDecl × Array Expr × Expr)) : VCGenM Bool := do
  let some (decl, xs, b) := filled | return true
  let v ← instantiateMVarsS b
  return !v.hasAnyFVar fun fv => !decl.lctx.contains fv && !xs.contains (.fvar fv)

/-- Give the holes that a rule left in the abstract program of the filled hole `filled` the hole's
context. A rule creates its holes in the goal's context, which also holds the variables that the run
introduced, such as the concrete state. The abstract program uses none of them (`filledInScope`),
and a table shares the program with the goals of the other cells. A hole of a delayed assignment
`?h xs := ?b` keeps its context, since `?b` occurs only behind `?h`. The maximal free variable of a
term with a hole depends on the hole's context, so the cache of `Sym.getMaxFVar?` starts afresh
after a change. -/
def restoreHoleScope (filled : Option (MetavarDecl × Array Expr × Expr)) : VCGenM Unit := do
  let some (decl, xs, b) := filled | return
  unless xs.isEmpty do return
  let outOfScope (e : Expr) := e.hasAnyFVar fun fv => !decl.lctx.contains fv
  let mut changed := false
  for mv in ← getMVars (← instantiateMVarsS b) do
    let d ← mv.getDecl
    unless d.kind matches .natural do continue
    unless d.lctx.numIndices > decl.lctx.numIndices do continue
    if outOfScope (← instantiateMVars d.type) then continue
    modifyMCtx (·.modifyExprMVarDecl mv fun d =>
      { d with lctx := decl.lctx, localInstances := decl.localInstances })
    changed := true
  if changed then
    (modify fun s => { s with maxFVar := {} } : Sym.SymM Unit)

/-- A fresh hole of type `β` in the current context. For a tuple type (`Prod`, `MProd`, `PProd`), the
hole is the pair of fresh holes for the components, so that a `match` on the witness reduces. -/
partial def mkWitnessHole (β : Expr) : VCGenM Expr := do
  let env ← getEnv
  let .const S us := β.getAppFn | return ← shareCommon (← mkFreshExprMVar β)
  unless S == ``Prod || S == ``MProd || S == ``PProd do return ← shareCommon (← mkFreshExprMVar β)
  let some info := getStructureInfo? env S | return ← shareCommon (← mkFreshExprMVar β)
  let ctor := getStructureCtor env S
  let params := β.getAppArgs
  unless params.size == ctor.numParams do return ← shareCommon (← mkFreshExprMVar β)
  let mut ty := ctor.type.instantiateLevelParams ctor.levelParams us
  for p in params do
    let .forallE _ _ body _ := ty | return ← shareCommon (← mkFreshExprMVar β)
    ty := body.instantiate1 p
  let mut fields := #[]
  for _ in [0:info.fieldNames.size] do
    let .forallE _ d body _ := ty | return ← shareCommon (← mkFreshExprMVar β)
    let f ← mkWitnessHole (← shareCommon d)
    fields := fields.push f
    ty := body.instantiate1 f
  mkAppNS (← mkConstS ctor.name us) (params ++ fields)

/-- Strategy 9b: introduce an existential on the `Prop` lattice. The witness of `pre ⊑ ∃ x, p x` is a
fresh hole `?x` in the goal's context (`mkWitnessHole`), and the goal continues as `pre ⊑ p ?x`. -/
def rhsExistsIntro? (goal : MVarId) (α pre rhs : Expr) : VCGenM (Option MVarId) := do
  unless α.isProp do return none
  let_expr Exists β p := rhs | return none
  let x ← mkWitnessHole β
  let px ← betaS p #[x]
  let target ← goal.getType
  let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS target.getAppFn (target.getAppArgs.set! 3 px))
  goal.assign (mkApp5 (mkConst ``Ascent.le_exists_of_le [← Sym.getLevel β]) β pre p x g)
  return some g.mvarId!

/-- Strategy 11b: split an `ite`/`dite`/`cond`/match program, or iota-reduce a matcher with a
concrete discriminant. -/
def wpMatch? (goal : MVarId) (info : WRPApp) :
    VCGenM (Option (List MVarId)) := do
  let some splitInfo ← liftMetaM <| Lean.Elab.Tactic.Do.getSplitInfo? info.prog | return none
  let rule ← mkBackwardRuleForSplitCached splitInfo info
  let (goal, filled) ← fillAbstractHole goal info
  let .goals goals ← rule.applyChecked goal m!"split rule for{indentExpr info.prog}"
    | throwError "Failed to apply split rule for {indentExpr info.prog}"
  unless ← filledInScope filled do
    throwError "ascend: the abstract split of{indentExpr info.prog}\nmentions a variable outside \
      the context of the abstract program"
  restoreHoleScope filled
  let mut simpGoals := #[]
  for g in goals do
    match ← simpGoalTelescope g with
    | .goal g' => simpGoals := simpGoals.push g'
    | .noProgress => simpGoals := simpGoals.push g
    | .closed => continue
  return some simpGoals.toList

/-- Strategy 11c: zeta-unfold a local let-bound fvar used as the program head. -/
def wpFVarZeta? (goal : MVarId) (info : WRPApp) :
    VCGenM (Option MVarId) := do
  let f := info.prog.getAppFn
  let some fvarId := f.fvarId? | return none
  let some val ← fvarId.getValue? | return none
  trace[Elab.Tactic.Do.vcgen] "fvar-zeta: {(← fvarId.getUserName)}"
  let prog ← shareCommonInc (val.betaRev info.prog.getAppRevArgs)
  return some (← replaceProgDefEq goal info prog)

/-- Stop or raise on a program with no applicable spec. With `errorOnMissingSpec` (default), raise a
hard error naming the program and the candidate specs; otherwise stop and emit the goal as a VC. -/
def stopOrErrorOnMissingSpec (prog monad : Expr) (thms : Array SpecTheorem) :
    VCGenM SolveResult := do
  unless (← read).errorOnMissingSpec do
    return .stop (.noSpecFound prog monad thms)
  if thms.isEmpty then
    throwError "No spec found for program {prog}."
  else
    throwError "No spec applicable to program {prog} in monad {monad}. \
      Candidates were {thms.map (·.proof)}."

/-- True iff the program matches the `until` pattern, in which case VC generation stops at this
goal. -/
def matchesUntilPattern (prog : Expr) : VCGenM Bool := do
  let some pat := (← read).untilPat? | return false
  if (← pat.match? prog).isSome then
    trace[Elab.Tactic.Do.vcgen] "`until` pattern matched program {prog}; stopping"
    return true
  return false

/--
Apply the selected `@[spec]` theorem `thm` to a spec-ready program `info.prog`. `none` when no
backward rule fits the goal's monad, or when the rule does not apply.

A spec with a conjunctive precondition applies directly. Otherwise the frame procedure `fp` runs,
with `providedFrame?` carrying the frame a `frames` clause pinned (both selected once per goal in
`applySpecs`). On `decline` the spec applies directly as well. On `commit` the solver applies the
frame rule to a copy of the goal, applies the spec at the weakest footprint, and runs the commit
continuation; see `FrameProc.lean`. When the spec does not apply to the footprint, the copy is
dropped and the candidate falls through.
-/
def applySpec (scope : Scope) (goal : MVarId) (info : WRPApp) (thm : SpecTheorem) :
    VCGenM (Option SolveResult) := do
  let some specRule ←
    try
      mkBackwardRuleFromSpecCached thm info |>.run
    catch ex =>
      throwError "Failed to construct rule {thm.proof} for {indentExpr info.prog}\n\
        error: {ex.toMessageData}\n\
        target:{indentExpr (← goal.getType)}\n\
        Pred:{indentExpr info.Pred}\n\
        excessArgs: {info.excessArgs}"
    | return none
  trace[Elab.Tactic.Do.vcgen] "Applying spec {thm.proof} for {info.prog}. Excess args: {info.excessArgs}"
  let saved ← (saveState : MetaM Meta.SavedState)
  let (goal, filled) ← fillAbstractHole goal info
  let .goals goals ← specRule.applyChecked goal m!"spec rule for{indentExpr info.prog}"
    | (saved.restore : MetaM Unit); return none
  -- The rule's abstract program may use only the hole's context and the hole's arguments.
  unless ← filledInScope filled do
    (saved.restore : MetaM Unit); return none
  restoreHoleScope filled
  return some (.goals scope goals)

/--
Handle a spec-ready program `info.prog`: apply the highest-priority `@[spec]` theorem whose backward
rule applies to the goal.

A candidate is passed over when no rule fits the goal's monad or when the rule does not apply, so a
spec guarded by an instance the call site does not provide gives way to a less general one, as does a
spurious candidate of the over-approximating discrimination tree.
-/
def applySpecs (scope : Scope) (goal : MVarId) (info : WRPApp) :
    VCGenM SolveResult := goal.withContext do
  let candidates ← SpecTheorems.findSpecs scope.specs info.prog
  for thm in candidates do
    if let some res ← applySpec scope goal info thm then
      return res
    trace[Elab.Tactic.Do.vcgen] "Failed to apply spec {thm.proof} for {info.prog}"
  stopOrErrorOnMissingSpec info.prog info.M candidates

/--
The main VC generation step. Operates on a plain `MVarId` with no knowledge of grind.
Returns `.goals subgoals` when the goal was decomposed, or a classification result
(`.noEntailment`, `.noProgramOrLatticeFoundInTarget`, etc.) when no further decomposition is
possible.

The function performs the following steps in order:

1. **Forall introduction**: If the target is a `∀`, simp it and introduce binders.
2. **Target-let handling**: zeta-substitute duplicable top-level lets, otherwise introduce them.
3. **Triple unfolding**: If the target is `⦃P⦄ x ⦃Q; E⦄`, unfold into `P ⊑ wp x Q E`.
4. **Syntactic rfl**: close `pre ⊑ rhs` by `PartialOrder.rel_refl` when both sides unify.
5. **Embedded pure precondition introduction**: lift a `⌜φ⌝` precondition into the local
   context, before state-argument introduction would apply it to the introduced arguments.
6. **State-argument introduction**: If the lattice carrier is a function type
   `σ₁ → ... → σₙ → Base`, introduce all excess state arguments.
7. **Bare pure precondition introduction**: on the `Prop` lattice, replace a `True`
   precondition by `⊤` and lift any other precondition into the local context.
8. **Lattice decomposition**: decompose a lattice connective on the RHS with `splitLatticeOp?`.
9. **Lifted-hypothesis discharge**: close a residual `pre ⊑ ⌜φ⌝` entailment against the most
    recently lifted precondition `h : φ` in the local context, cached in `Scope.lastLiftedPre?`.
10. **WP decomposition**: when the RHS is `wp e post eposts s₁ ... sₙ`, in order:
    introduce/zeta program-head lets, split `ite`/`dite`/match, zeta-unfold fvar program heads,
    reduce projection heads, and finally apply a registered `@[spec]` theorem.
-/
def solve (scope : Scope) (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  if ← outOfFuel then return .stop .outOfFuel
  let target ← goal.getType
  trace[Elab.Tactic.Do.vcgen] "🎯 Target: {target}"

  -- Phase 1: simplify `target` until it is of the form `pre ⊑ rhs`.
  if let some g ← consumeMData? goal target then return .goals scope [g]
  if let some g ← consumeBinderNameHint? goal target then return .goals scope [g]
  if let some gs ← forallIntro? goal target then return .goals scope gs
  if let some g ← targetLetIntro? goal target then return .goals scope [g]
  if let some g ← tripleUnfold? goal target then return .goals scope [g]
  if let some g ← bareWPToLe? goal target then return .goals scope [g]
  if let some gs ← liftedHypBare? scope goal target then return .goals scope gs
  if let some g ← instantiateGoal? goal target then return .goals scope [g]

  let_expr PartialOrder.rel α _ pre rhs := target
    | return .stop (.noEntailment target)

  -- Phase 2: close reflexive goals, then drive `pre` toward `⊤`, lifting any pure content so a
  -- later spec application sees a `⊤` precondition.
  if let some gs ← rfl? goal then return .goals scope gs
  if let some (scope, gs) ← normalizePre? scope goal α pre target then return .goals scope gs

  -- Collect new local specs before any strategy that may emit multiple subgoals
  -- (`wpMatch?`, `splitLatticeOp?`) or apply a registered spec (`applySpec`).
  let scope ← scope.collectLocalSpecs goal

  -- Phase 3: shape the `rhs` (decompose a lattice connective or a forall, then discharge a
  -- residual entailment against the lifted hypothesis).
  if let some g ← rhsLet? goal rhs then return .goals scope [g]
  if let some gs ← splitLatticeOp? goal rhs then return .goals scope gs
  if let some gs ← splitForallLe? goal rhs then return .goals scope gs
  if let some g ← rhsExistsIntro? goal α pre rhs then return .goals scope [g]
  if let some gs ← liftedHyp? scope goal α pre rhs then return .goals scope gs

  -- Phase 4: wp decomposition. The program-shape steps below all consume one unit of fuel
  -- (the `stepLimit` config option) when they make progress.
  if let some info := isWRPApp? rhs then
    trace[Elab.Tactic.Do.vcgen] "📜 Program: {info.prog}"
    -- Stop if the program matches the `until` pattern.
    if ← matchesUntilPattern info.prog then
      return .stop (.untilPatternMatched info.M)
    if let some g ← wpConsumeMData? goal info then
      return .goals scope [g]
    if let some g ← wpReduceHead? goal info then
      burnOne
      return .goals scope [g]
    if let some (scope, gs) ← wpLet? scope goal info then
      burnOne
      return .goals scope gs
    if let some gs ← wpSimpStateArgs? goal info then
      return .goals scope gs
    if let some gs ← wpMatch? goal info then
      burnOne
      return .goals scope gs
    if let some gs ← wpJump? scope goal info then
      burnOne
      return .goals scope gs
    if let some g ← wpFVarZeta? goal info then
      burnOne
      return .goals scope [g]
    let f := info.prog.getAppFn
    if f.isConst || f.isFVar then
      burnOne
      return ← applySpecs scope goal info
    return ← stopOrErrorOnMissingSpec info.prog info.M #[]

  return .stop (.noProgress pre rhs)


end Lean.Elab.Tactic.VCGen.Ascend
