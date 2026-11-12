import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.Util
import Lean.Elab.Tactic.VCGen.Entails
import Lean.Meta.Sym.Grind
import Ascent.PureRefinement

/-!
# The `PureRefinement` solver

`@[ascend_pure]` registers a rule whose conclusion is `PureRefinement cv av P Q`, keyed on `cv`.
Each environment entry `hx : PureRefinement c x True Q` contributes two backward rules: `hx`
itself, keyed on `c`, and `PureRefinement.rel hx : Q c x`, keyed on its type. The entries are the
hypotheses of the local context in the `simp` normal form of the run, and the conjuncts of such
hypotheses. `Refinement.pure_rel` introduces an entry at each bind, with a variable `c`. An entry
with a compound `c`, such as the register read `t.regs.get64 .rsi` of a state `t`, abstracts that
term.

The solver closes a goal `PureRefinement cv ?av ?P Q` by recursion over `cv`, at the `simp`
normal form of each `cv`, and also under a `⊤ ⊑` precondition. It applies the
environment rules for `cv` and then the `@[ascend_pure]` rules by priority, solves the premises in
order, and backtracks to the next rule when a premise fails. An `@[ascend_pure]` rule without
premises applies only if its abstract value mentions no free variable of the `c` of an environment
entry.

The solver solves the goal at a fresh precondition `?P₀` and simplifies `?P₀` to `P` with the
`simp` methods of the run. A goal whose guard is a hole gets `P`; a goal with a guard `P_goal`
gets `P` by the consequence rule `PureRefinement.weaken_pre`, with the verification condition
`P_goal → P`. A verification condition `Q c x` closes by the rule
`PureRefinement.rel hx`.
-/

open Lean Meta Sym Sym.Internal

namespace Lean.Elab.Tactic.VCGen.Ascend

/-- A `PureRefinement` rule: an `@[ascend_pure]` theorem or the rule of an environment entry. -/
structure PureRule where
  /-- The pattern of the key: `cv` for a rule that concludes `PureRefinement cv av P Q`, and the
  whole conclusion for the rule `PureRefinement.rel hx`. -/
  key : Sym.Pattern
  rule : BackwardRule
  priority : Nat := 0

instance : Inhabited PureRule where
  default := { key := default, rule := { expr := default, pattern := default, resultPos := [] } }

instance : BEq PureRule where
  beq a b := a.rule.expr == b.rule.expr

/-- The `cv` argument of a conclusion `PureRefinement cv av P Q`. -/
def pureRefinementCV? (type : Expr) : Option Expr :=
  if type.isAppOfArity ``Ascent.PureRefinement 6 then type.getArg! 2 else none

def selectCV (type : Expr) : MetaM (Expr × Unit) := do
  let some cv := pureRefinementCV? type
    | throwError "@[ascend_pure]: the conclusion{indentExpr type}\nis not `PureRefinement cv av P Q`"
  return (cv, ())

def mkPureRule (declName : Name) (priority : Nat) : MetaM PureRule := do
  let (key, _) ← Sym.mkPatternFromDeclWithKey declName selectCV
  return { key, rule := ← mkBackwardRuleFromDecl declName, priority }

initialize ascendPureExt : SimpleScopedEnvExtension PureRule (DiscrTree PureRule) ←
  registerSimpleScopedEnvExtension {
    name := `ascendPureMap
    initial := DiscrTree.empty
    addEntry := fun d r => Sym.insertPattern d r.key r }

initialize registerBuiltinAttribute {
  name := `ascend_pure
  descr := "a `PureRefinement cv av P Q` rule for the value abstraction of the ascend fork of vcgen"
  add := fun declName stx kind => do
    let prio ← getAttrParamOptPrio stx[1]
    ascendPureExt.add (← MetaM.run' (mkPureRule declName prio)) kind
}

/-- The rules of the environment entries. `seen` holds every local declaration already scanned,
and `outer` the variables in scope of the abstract program. `keys` holds the concrete variable `c`
of every entry, and for an entry with a compound `c`, the variables of `c` outside `outer`. -/
structure PureEnv where
  seen : Std.HashSet FVarId := {}
  outer : Std.HashSet FVarId := {}
  keys : Std.HashSet FVarId := {}
  /-- The rule `hx`, keyed on `c`. -/
  entries : DiscrTree PureRule := DiscrTree.empty
  /-- The rule `PureRefinement.rel hx`, keyed on `Q c x`. -/
  rels : DiscrTree PureRule := DiscrTree.empty
  deriving Inhabited

initialize pureEnvExt : SymExtension PureEnv ← registerSymExtension (pure {})

/-- The `Refinement` specs of the invocation, as backward rules for `Refinement` premises. -/
initialize refinementSpecsExt : SymExtension (Array BackwardRule) ← registerSymExtension (pure #[])

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
  if type.isAppOfArity ``Ascent.PureRefinement 6 && type.getArg! 4 matches .const ``True _ then
    return #[(type, h)]
  let_expr And a b := type | return #[]
  let ha ← mkAppNS (← mkConstS ``And.left []) #[a, b, h]
  let hb ← mkAppNS (← mkConstS ``And.right []) #[a, b, h]
  return (← pureEntries a ha) ++ (← pureEntries b hb)

/-- Add the rules of the local declarations that the environment has not seen. The entries of a
hypothesis are read from its type in the `simp` normal form of the run. A local context extends a
context that the environment scanned, so the scan stops at the last declaration that it has seen. -/
def updatePureEnv : VCGenM PureEnv := do
  let lctx ← getLCtx
  let mut env ← pureEnvExt.getState
  let mut i := lctx.decls.size
  while i > 0 do
    i := i - 1
    let some decl := lctx.decls[i]! | continue
    if env.seen.contains decl.fvarId then break
    env := { env with seen := env.seen.insert decl.fvarId }
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
      let entry : PureRule := { key, rule := ← (← mkBackwardRuleFromExpr hx).shareCommon }
      let args := type.getAppArgs
      let rel ← mkAppNS (← mkConstS ``Ascent.PureRefinement.rel type.getAppFn.constLevels!)
        #[args[0]!, args[1]!, args[2]!, args[3]!, args[5]!, hx]
      let relRule ← (← mkBackwardRuleFromExpr rel).shareCommon
      env := { env with
        keys := if c.isFVar then env.keys.insert c.fvarId! else
          (collectFVars {} c).fvarIds.foldl (fun ks x => if env.outer.contains x then ks else ks.insert x)
            env.keys
        entries := Sym.insertPattern env.entries entry.key entry
        rels := Sym.insertPattern env.rels relRule.pattern { key := relRule.pattern, rule := relRule } }
  pureEnvExt.modifyState fun _ => env
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
      let ofCvEq ← mkConstS ``Ascent.PureRefinement.of_cv_eq type.getAppFn.constLevels!
      goal.assign (← mkAppNS ofCvEq #[args[0]!, args[1]!, cv₀, args[3]!, args[4]!, args[5]!, cv, g, e])
      pure (g.mvarId!, type')
  let mctx ← getMCtx
  let entries := Sym.getMatch mctx env.entries cv
  let candidates := entries ++ (Sym.getMatch mctx rules cv).qsort (·.priority > ·.priority)
  let mut failure := cv
  for h : i in [0:candidates.size] do
    let r := candidates[i]
    let saved ← (saveState : MetaM Meta.SavedState)
    let .goals premises ← r.rule.apply goal | continue
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
      && (← instantiateMVarsIfMVarAppS rhs).isAppOfArity ``Ascent.PureRefinement 6
  return type.isAppOfArity ``Ascent.PureRefinement 6

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
    if let some t ← solveCore (ascendPureExt.getState (← getEnv)) (← updatePureEnv) aux.mvarId! then
      throwError "ascend: no `@[ascend_pure]` rule abstracts{indentExpr t}"
    let av₀ ← instantiateMVarsS av₀
    let P₀ ← instantiateMVarsS P₀
    let (av, eav?) ← simpRun av₀
    let (P, eP?) ← simpRun P₀
    let us := head.constLevels!
    let mut prf := aux
    if let some eP := eP? then
      prf ← mkAppNS (← mkConstS ``Ascent.PureRefinement.of_pre_eq us)
        #[args[0]!, args[1]!, args[2]!, av₀, P₀, P, args[5]!, prf, eP]
    if let some eav := eav? then
      prf ← mkAppNS (← mkConstS ``Ascent.PureRefinement.of_val_eq us)
        #[args[0]!, args[1]!, args[2]!, av₀, P, args[5]!, av, prf, eav]
    let av' ← instantiateMVarsS args[3]!
    let eqType ← mkAppNS (← mkConstS ``Eq [.succ us[1]!]) #[args[1]!, av, av']
    let hval ← shareCommon (← mkFreshExprSyntheticOpaqueMVar eqType (tag := `hval))
    prf ← mkAppNS (← mkConstS ``Ascent.PureRefinement.of_val_eq us)
      #[args[0]!, args[1]!, args[2]!, av, P, args[5]!, av', prf, hval]
    let newGoals := [hval.mvarId!]
    if ← isDefEqS args[4]! P then
      goal.assign prf
      return newGoals
    let Pgoal ← instantiateMVarsS args[4]!
    let hpreType ← mkForallS `h .default Pgoal P
    let hpre ← shareCommon (← mkFreshExprSyntheticOpaqueMVar hpreType (tag := `hpre))
    goal.assign (← mkAppNS (← mkConstS ``Ascent.PureRefinement.weaken_pre us)
      #[args[0]!, args[1]!, args[2]!, av, P, Pgoal, args[5]!, prf, hpre])
    return hpre.mvarId! :: newGoals

/-- Close the premise `goal : ⦃P⦄ c ⪯[ρ] a ⦃Q; E⦄` of a rule with the first `Refinement` spec of the
invocation that unifies with it. Returns the premises of that spec. -/
def solveRefinement (goal : MVarId) : VCGenM (Option (List MVarId)) := do
  for rule in ← refinementSpecsExt.getState do
    if let .goals gs ← rule.apply goal then return some gs
  return none

/-- `true` iff `goal` is a `Refinement` goal. -/
def isRefinementGoal (goal : MVarId) : SymM Bool := do
  return (← instantiateMVarsIfMVarAppS (← goal.getType)).isAppOf ``Ascent.Refinement

/-- Close a verification condition `Q c x` with the rule `PureRefinement.rel hx` of an environment
entry `hx`. -/
def closeByEntry (goal : MVarId) : VCGenM Bool := goal.withContext do
  let env ← updatePureEnv
  let type ← instantiateMVarsS (← goal.getType)
  for r in Sym.getMatch (← getMCtx) env.rels type do
    if (← r.rule.apply goal) matches .goals [] then return true
  return false

end Lean.Elab.Tactic.VCGen.Ascend
