import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.Util
import Lean.Elab.Tactic.VCGen.Entails
import Lean.Meta.Sym.Grind
import Distillery.PureRefinement

/-!
# The `PureRefinement` solver

`@[distill_pure]` registers a rule whose conclusion is `PureRefinement cv av P Q`, keyed on `cv`.
Each environment entry `hx : PureRefinement c x True Q` contributes two backward rules: `hx`
itself, keyed on `c`, and `PureRefinement.rel hx : Q c x`, keyed on its type. The entries are the
hypotheses of the local context in the `simp` normal form of the run, and the conjuncts of such
hypotheses. `Refinement.pure_rel` introduces an entry at each bind, with a variable `c`. An entry
with a compound `c`, such as the register read `t.regs.get64 .rsi` of a state `t`, abstracts that
term. Of several entries for one term, the solver tries the most recent one first. Each local context
has its own environment, so a branch sees only the entries of that branch.

The solver closes a goal `PureRefinement cv ?av ?P Q` by recursion over `cv`, at the `simp`
normal form of each `cv`, and also under a `⊤ ⊑` precondition. It applies the
environment rules for `cv` and then the `@[distill_pure]` rules by priority, solves the premises in
order, and backtracks to the next rule when a premise fails. An `@[distill_pure]` rule without
premises applies only if its abstract value mentions no free variable of the `c` of an environment
entry.

The solver solves the goal at a fresh precondition `?P₀` and simplifies `?P₀` to `P` with the
`simp` methods of the run. A goal whose guard is a hole gets `P`; a goal with a guard `P_goal`
gets `P` by the consequence rule `PureRefinement.weaken_pre`, with the verification condition
`P_goal → P`. A verification condition `Q c x` closes by the rule
`PureRefinement.rel hx`.
-/

open Lean Meta Sym Sym.Internal

namespace Lean.Elab.Tactic.VCGen.Distill

/-- A `PureRefinement` rule: an `@[distill_pure]` theorem or the rule of an environment entry. -/
structure PureRule where
  /-- The pattern of the key: `cv` for a rule that concludes `PureRefinement cv av P Q`, and the
  whole conclusion for the rule `PureRefinement.rel hx`. -/
  key : Sym.Pattern
  rule : BackwardRule
  priority : Nat := 0
  /-- The index of the local declaration of an environment entry. -/
  index : Nat := 0

instance : Inhabited PureRule where
  default := { key := default, rule := { expr := default, pattern := default, resultPos := [] } }

instance : BEq PureRule where
  beq a b := a.rule.expr == b.rule.expr

/-- The `cv` argument of a conclusion `PureRefinement cv av P Q`. -/
def pureRefinementCV? (type : Expr) : Option Expr :=
  if type.isAppOfArity ``Distillery.PureRefinement 6 then type.getArg! 2 else none

def selectCV (type : Expr) : MetaM (Expr × Unit) := do
  let some cv := pureRefinementCV? type
    | throwError "@[distill_pure]: the conclusion{indentExpr type}\nis not `PureRefinement cv av P Q`"
  return (cv, ())

def mkPureRule (declName : Name) (priority : Nat) : MetaM PureRule := do
  let (key, _) ← Sym.mkPatternFromDeclWithKey declName selectCV
  return { key, rule := ← mkBackwardRuleFromDecl declName, priority }

initialize distillPureExt : SimpleScopedEnvExtension PureRule (DiscrTree PureRule) ←
  registerSimpleScopedEnvExtension {
    name := `distillPureMap
    initial := DiscrTree.empty
    addEntry := fun d r => Sym.insertPattern d r.key r }

initialize registerBuiltinAttribute {
  name := `distill_pure
  descr := "a `PureRefinement cv av P Q` rule for the value abstraction of the distill fork of vcgen"
  add := fun declName stx kind => do
    let prio ← getAttrParamOptPrio stx[1]
    distillPureExt.add (← MetaM.run' (mkPureRule declName prio)) kind
}

/-- The rules of the environment entries of a local context. `outer` holds the variables in scope of
the abstract program. `keys` holds the concrete variable `c` of every entry, and for an entry with a
compound `c`, the variables of `c` outside `outer`. `hyps` holds the hypotheses of the entries. -/
structure PureEnv where
  outer : Std.HashSet FVarId := {}
  keys : Std.HashSet FVarId := {}
  hyps : Array FVarId := #[]
  /-- The rule `hx`, keyed on `c`. -/
  entries : DiscrTree PureRule := DiscrTree.empty
  /-- The rule `PureRefinement.rel hx`, keyed on `Q c x`. -/
  rels : DiscrTree PureRule := DiscrTree.empty
  deriving Inhabited

/-- The environments of the run: `base`, the environment of the empty context, and for each local
declaration `d` that a scan reached, the environment of the context that ends in `d`. -/
structure PureEnvs where
  base : PureEnv := {}
  byLast : Std.HashMap FVarId PureEnv := {}
  deriving Inhabited

initialize pureEnvExt : SymExtension PureEnvs ← registerSymExtension (pure {})

/-- A `Refinement` spec of the invocation: its proof with the metavariables abstracted, its level
parameters, and the number of leading binders of its type. -/
structure RefinementSpec where
  expr : Expr
  levelParams : List Name
  numBinders : Nat

/-- The `Refinement` specs of the invocation, for `Refinement` premises. -/
initialize refinementSpecsExt : SymExtension (Array RefinementSpec) ← registerSymExtension (pure #[])

/-- Simplify `e` with the `simp` methods of the run. Returns the result and a proof of
`e = result`, or `none` if `simp` makes no progress. -/
def simpRun (e : Expr) : VCGenM (Expr × Option Expr) := do
  let some methods := (← read).simpMethods | return (e, none)
  let (result, simpState') ← Sym.Simp.SimpM.run (Sym.Simp.simp e) methods {} (← get).simpState
  modify fun s => { s with simpState := simpState' }
  match result with
  | .rfl .. => return (e, none)
  | .step e' proof .. => return (← shareCommon e', some (← shareCommon proof))

/-- The entries `PureRefinement c x True Q` that the proof `h : type` contains, with their proofs:
`h` itself, and the entries of both sides of a conjunction. -/
partial def pureEntries (type h : Expr) : SymM (Array (Expr × Expr)) := do
  let type ← instantiateMVarsS type
  if type.isAppOfArity ``Distillery.PureRefinement 6 && type.getArg! 4 matches .const ``True _ then
    return #[(type, h)]
  let_expr And a b := type | return #[]
  let ha ← mkAppNS (← mkConstS ``And.left []) #[a, b, h]
  let hb ← mkAppNS (← mkConstS ``And.right []) #[a, b, h]
  return (← pureEntries a ha) ++ (← pureEntries b hb)

/-- The environment of the current local context. It extends the environment of the longest prefix
of the context that a scan reached by the rules of the later declarations, so the environment of a
branch holds only the entries of that branch. An environment whose hypotheses the context lost,
such as by a `subst`, does not count as a prefix. The entries of a hypothesis are read from its type
in the `simp` normal form of the run. -/
def updatePureEnv : VCGenM PureEnv := do
  let lctx ← getLCtx
  let envs ← pureEnvExt.getState
  let mut i := lctx.decls.size
  let mut env := envs.base
  let mut todo := #[]
  while i > 0 do
    i := i - 1
    let some decl := lctx.decls[i]! | continue
    if let some e := envs.byLast[decl.fvarId]? then
      if e.hyps.all lctx.contains then
        env := e
        break
    todo := todo.push decl
  if todo.isEmpty then return env
  for decl in todo.reverse do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVarsS decl.type
    unless (← Sym.inferType type).isProp do continue
    let h ← mkFVarS decl.fvarId
    let (type', e?) ← simpRun type
    let h ← match e? with
      | some e => mkAppNS (← mkConstS ``Eq.mp [0]) #[type, type', e, h]
      | none => pure h
    for (type, h) in ← pureEntries type' h do
      let c := type.getArg! 2
      -- The pattern builders infer the type of `hx`, and the declared type can mention assigned
      -- metavariables, so `hx` is stated at its instantiated type.
      let hx ← mkAppNS (← mkConstS ``id [0]) #[type, h]
      let (key, _) ← Sym.mkPatternFromExprWithKey hx [] selectCV
      let entry : PureRule :=
        { key, rule := ← (← mkBackwardRuleFromExpr hx).shareCommon, index := decl.index }
      let args := type.getAppArgs
      let rel ← mkAppNS (← mkConstS ``Distillery.PureRefinement.rel type.getAppFn.constLevels!)
        #[args[0]!, args[1]!, args[2]!, args[3]!, args[5]!, hx]
      let relRule ← (← mkBackwardRuleFromExpr rel).shareCommon
      env := { env with
        keys := if c.isFVar then env.keys.insert c.fvarId! else
          (collectFVars {} c).fvarIds.foldl (fun ks x => if env.outer.contains x then ks else ks.insert x)
            env.keys
        hyps := env.hyps.push decl.fvarId
        entries := Sym.insertPattern env.entries entry.key entry
        rels := Sym.insertPattern env.rels relRule.pattern { key := relRule.pattern, rule := relRule } }
  let last := todo[0]!.fvarId
  pureEnvExt.modifyState fun envs => { envs with byLast := envs.byLast.insert last env }
  return env

/-- Solve the goal `PureRefinement cv ?av ?P Q` from the environment and the rules. Returns `none`
on success, and otherwise the subterm of `cv` that no rule abstracts. -/
partial def solveCore (rules : DiscrTree PureRule) (env : PureEnv) (goal : MVarId) :
    VCGenM (Option Expr) := goal.withContext do
  let type ← instantiateMVarsS (← goal.getType)
  let some cv₀ := pureRefinementCV? type | return some type
  let (cv, e?) ← simpRun cv₀
  let (goal, type) ← match e? with
    | none => pure (goal, type)
    | some e =>
      let args := type.getAppArgs
      let type' ← mkAppNS type.getAppFn (args.set! 2 cv)
      let g ← shareCommon (← mkFreshExprMVar type')
      let ofCvEq ← mkConstS ``Distillery.PureRefinement.of_cv_eq type.getAppFn.constLevels!
      goal.assign (← mkAppNS ofCvEq #[args[0]!, args[1]!, cv₀, args[3]!, args[4]!, args[5]!, cv, g, e])
      pure (g.mvarId!, type')
  let mctx ← getMCtx
  -- The most recent entry of a concrete term comes first: a later read of the state rebinds it.
  let entries := (Sym.getMatch mctx env.entries cv).qsort (·.index > ·.index)
  if entries.isEmpty then
    if let some val ← cv.fvarId?.bindM (·.getValue?) then
      let val ← shareCommon val
      trace[Elab.Tactic.Do.vcgen] "pure goal {type}: the value of the local definition {cv}"
      let g ← shareCommon (← mkFreshExprMVar (← mkAppNS type.getAppFn (type.getAppArgs.set! 2 val)))
      goal.assign g
      return ← solveCore rules env g.mvarId!
  let candidates := entries ++ (Sym.getMatch mctx rules cv).qsort (·.priority > ·.priority)
  let mut failure := cv
  trace[Elab.Tactic.Do.vcgen] "pure goal {type}: {entries.size} entries, {candidates.size} candidates"
  for h : i in [0:candidates.size] do
    let r := candidates[i]
    let saved ← (saveState : MetaM Meta.SavedState)
    let .goals premises ← r.rule.apply goal
      | trace[Elab.Tactic.Do.vcgen] "pure rule {r.rule.expr} does not apply"
        (saved.restore : MetaM Unit)
        continue
    trace[Elab.Tactic.Do.vcgen] "pure rule {r.rule.expr} applies with {premises.length} premises"
    if entries.size ≤ i && premises.isEmpty &&
        (← instantiateMVarsS (type.getArg! 3)).hasAnyFVar env.keys.contains then
      (saved.restore : MetaM Unit)
      continue
    let mut inner := none
    for p in premises do
      inner ← solveCore rules env p
      if inner.isSome then break
    let some t := inner | return none
    failure := t
    (saved.restore : MetaM Unit)
  return some failure

/-- `true` iff `goal` is a `PureRefinement` goal, or a `PureRefinement` goal under `⊤ ⊑`. -/
def isPureRefinementGoal (goal : MVarId) : SymM Bool := do
  let type ← instantiateMVarsIfMVarAppS (← goal.getType)
  if let some (.sort .zero, _, pre, rhs) := type.app4? ``Lean.Order.PartialOrder.rel then
    return (← instantiateMVarsIfMVarAppS pre).isAppOf ``Lean.Order.top
      && (← instantiateMVarsIfMVarAppS rhs).isAppOfArity ``Distillery.PureRefinement 6
  return type.isAppOfArity ``Distillery.PureRefinement 6

/-- Close the goal `PureRefinement cv ?av P_goal Q`. The precondition and the abstract value are
simplified with the `simp` methods of the run. The solution's precondition `P` meets `P_goal` by
the consequence rule `PureRefinement.weaken_pre`: when `P_goal` is not `P`, the premise
`hpre : P_goal → P` is a new goal. The solution meets the abstract value `av'` of the goal by
`PureRefinement.of_val_eq`, with the new goal `av = av'`. `cleanupVC` closes that goal by `rfl`
and assigns a hole in `av'`.
Throws if no rule abstracts a subterm of `cv`. -/
def solvePureRefinement (goal : MVarId) : VCGenM (List MVarId) := do
  let goal ← elimTopPre goal
  goal.withContext do
    let type ← instantiateMVarsS (← goal.getType)
    let head := type.getAppFn
    let args := type.getAppArgs
    let av₀ ← shareCommon (← mkFreshExprMVar args[1]!)
    let P₀ ← shareCommon (← mkFreshExprMVar (mkSort .zero))
    let aux ← shareCommon (← mkFreshExprMVar (← mkAppNS head ((args.set! 3 av₀).set! 4 P₀)))
    if let some t ← solveCore (distillPureExt.getState (← getEnv)) (← updatePureEnv) aux.mvarId! then
      throwError "distill: no `@[distill_pure]` rule abstracts{indentExpr t}"
    let av₀ ← instantiateMVarsS av₀
    let P₀ ← instantiateMVarsS P₀
    let (av, eav?) ← simpRun av₀
    let (P, eP?) ← simpRun P₀
    let us := head.constLevels!
    let mut prf := aux
    if let some eP := eP? then
      prf ← mkAppNS (← mkConstS ``Distillery.PureRefinement.of_pre_eq us)
        #[args[0]!, args[1]!, args[2]!, av₀, P₀, P, args[5]!, prf, eP]
    if let some eav := eav? then
      prf ← mkAppNS (← mkConstS ``Distillery.PureRefinement.of_val_eq us)
        #[args[0]!, args[1]!, args[2]!, av₀, P, args[5]!, av, prf, eav]
    let av' ← instantiateMVarsS args[3]!
    let eqType ← mkAppNS (← mkConstS ``Eq [.succ us[1]!]) #[args[1]!, av, av']
    let hval ← shareCommon (← mkFreshExprSyntheticOpaqueMVar eqType (tag := `hval))
    prf ← mkAppNS (← mkConstS ``Distillery.PureRefinement.of_val_eq us)
      #[args[0]!, args[1]!, args[2]!, av, P, args[5]!, av', prf, hval]
    let newGoals := [hval.mvarId!]
    if ← isDefEqS args[4]! P then
      goal.assign prf
      return newGoals
    let Pgoal ← instantiateMVarsS args[4]!
    let hpreType ← mkForallS `h .default Pgoal P
    let hpre ← shareCommon (← mkFreshExprSyntheticOpaqueMVar hpreType (tag := `hpre))
    goal.assign (← mkAppNS (← mkConstS ``Distillery.PureRefinement.weaken_pre us)
      #[args[0]!, args[1]!, args[2]!, av', P, Pgoal, args[5]!, prf, hpre])
    return hpre.mvarId! :: newGoals

/-- The number of leading universal quantifiers of `e`. -/
def numForalls : Expr → Nat
  | .forallE _ _ b _ => numForalls b + 1
  | _ => 0

/-- Close the premise `goal : ∀ xs, ⦃P⦄ c ⪯[ρ] a ⦃Q; E⦄` of a rule with the first `Refinement` spec
of the invocation that unifies with it. The spec's backward rule keeps its last binders, one for
each binder of `xs`, so that the unifier matches the two quantifiers: holes applied to `xs`, such as
the abstract program, are patterns over binders of the unification. Returns the premises of the
spec. -/
def solveRefinement (goal : MVarId) : VCGenM (Option (List MVarId)) := do
  let specs ← refinementSpecsExt.getState
  if specs.isEmpty then return none
  let k := numForalls (← instantiateMVarsIfMVarAppS (← goal.getType))
  for spec in specs do
    unless k ≤ spec.numBinders do continue
    let rule ← Sym.mkBackwardRuleFromExpr spec.expr spec.levelParams (num? := some (spec.numBinders - k))
    if let .goals gs ← rule.apply goal then return some gs
  return none

/-- `true` iff `goal` is a `Refinement` goal under universal quantifiers. -/
def isRefinementGoal (goal : MVarId) : SymM Bool := do
  let rec body : Expr → Expr
    | .forallE _ _ b _ => body b
    | e => e
  return body (← instantiateMVarsIfMVarAppS (← goal.getType)) |>.isAppOf ``Distillery.Refinement

/-- Close a verification condition `Q c x` with the rule `PureRefinement.rel hx` of an environment
entry `hx`. -/
def closeByEntry (goal : MVarId) : VCGenM Bool := goal.withContext do
  let env ← updatePureEnv
  let type ← instantiateMVarsS (← goal.getType)
  for r in Sym.getMatch (← getMCtx) env.rels type do
    if (← r.rule.apply goal) matches .goals [] then return true
  return false

end Lean.Elab.Tactic.VCGen.Distill
