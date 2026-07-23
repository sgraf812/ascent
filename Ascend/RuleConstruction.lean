import Ascend.Context
import Ascent.Corres.RTriple

/-!
# Rule compilation and application

A registered spec is compiled once per phase into an apply-ready backward rule, and applied
per goal by pattern matching, so no application-time work scales with the size of the goal's
value terms.

**Compilation** (`compileRule`, cached by spec name and the phase's `γ`): project
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

/-- Sharing-preserving `instantiateMVarsIfMVarApp`: `Meta.instantiateMVarsIfMVarApp` returns
un-interned nodes, breaking the `SymM` maximal-sharing invariant that later matching relies on.
`Sym.instantiateMVarsS` re-interns; the `hasMVar` guard skips the traversal when nothing is
assigned (`instantiateMVarsS` also short-circuits, but the head test is cheaper still). -/
def instantiateMVarsIfMVarAppS (e : Expr) : SymM Expr := do
  if e.getAppFn.isMVar then Sym.instantiateMVarsS e else return e

/-- Replace `goal`'s target with the definitionally equal `target`, re-interning it so the
`SymM` maximal-sharing invariant holds for the matcher. `shareCommonInc` interns only the fresh
spine nodes; the shared children are looked up directly. Unlike `MVarId.replaceTargetDefEq`,
the old target is not read back (which would walk the goal's assigned synthesis metavariables). -/
def setTargetRaw (goal : MVarId) (target : Expr) : SymM MVarId := do
  let target ← shareCommonInc target
  let ng ← mkFreshExprSyntheticOpaqueMVar target (← goal.getTag)
  goal.assign ng
  return ng.mvarId!

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

/-- The monad of a program type `M α`: peel the value type. A program type that is not an
application (an undetermined metavariable, or a non-monadic `WP` carrier) has no value type to
peel and is compared whole. -/
private def monadOf (progTy : Expr) : Expr :=
  if progTy.isApp then progTy.appFn! else progTy

/-- Compile `spec` to apply-ready form against the phase of the goal `g`. -/
private def compileRule (si : SpecInfo) (g : RWPApp) : AscendM (Option CachedRule) := do
  let rule ← mkConstWithFreshMVarLevels si.declName
  -- Non-reducing: at the `Prop` lattice the `RTriple` conclusion would reduce to an
  -- implication and the telescope would consume the precondition as a binder.
  let (mvs, bis, concl) ← forallMetaTelescope (← Meta.inferType rule)
  let some (relTy, prf) ← conclusionProof rule mvs concl | return none
  let some ruleRwp := parseRWP? relTy.appArg! | return none
  -- Pin the phase, and the monads: compare the monad `M` of each program type `M α` via
  -- `monadOf` (peeling the value type), so a parameterized monad like `Except ε` is not
  -- over-stripped to its head as `getAppFn` would.
  for i in phasePositions do
    unless ← isDefEqGuarded ruleRwp.args[i]! g.args[i]! do return none
  unless ← isDefEqGuarded (monadOf ruleRwp.AProg) (monadOf g.AProg) do return none
  unless ← isDefEqGuarded (monadOf ruleRwp.CProg) (monadOf g.CProg) do return none
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
      -- Substitute eagerly: this is compile-time work, shared by all applications.
      pure (some (← abstractMVars (← instantiateMVars lam)))
  -- The auxiliary theorem `∀ P' (h : P' ⊑ pre'), P' ⊑ rwp …`, leaving the precondition entailment
  -- as the sole subgoal; `solve` decomposes it through the lattice-connective split rules.
  let relTy ← instantiateMVars relTy
  let_expr rel@Lean.Order.PartialOrder.rel relCarrier relInst rulePre ruleRhs := relTy | return none
  let pre' ← instantiateMVars rulePre
  let carrier ← instantiateMVars g.CPred
  -- The auxiliary theorem `∀ P' (h : P' ⊑ pre'), P' ⊑ rwp …`, leaving the precondition entailment
  -- as the sole subgoal; `solve` decomposes it through the lattice-connective split rules.
  let aux ← withLocalDeclD `P' carrier fun P' => do
    withLocalDeclD `h (mkApp4 rel relCarrier relInst P' pre') fun h => do
      let relTrans := mkConst ``Lean.Order.PartialOrder.rel_trans rel.constLevels!
      mkLambdaFVars #[P', h] <|
        mkApp7 relTrans relCarrier relInst P' pre' ruleRhs h (← instantiateMVars prf)
  -- Substitute eagerly: this is compile-time work, shared by all applications.
  let res ← abstractMVars (← instantiateMVars aux)
  let rule ← mkBackwardRuleFromExpr res.expr res.paramNames.toList
  -- Internalize the rule (and the template) into the Sym object table, so apply-time
  -- comparisons hit pointer fast paths and the subgoals it builds are pre-shared.
  let rule ← rule.shareCommon
  let template? ← template?.mapM fun tmpl =>
    return { tmpl with expr := ← shareCommonInc tmpl.expr }
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
  let goalA ← instantiateMVarsIfMVarAppS g.a
  let .mvar mvarId := goalA.getAppFn | return some none
  -- Values are substituted once, here, where they enter the goal: rule application binds by
  -- metavariable assignment, and every later inspection would otherwise re-walk the
  -- assigned-mvar chain. The previous leaf cleaned its prefix, so this is one layer per leaf.
  let ts ← goalA.getAppArgs.mapM (instantiateMVars ·)
  let some tmpl := c.template? | return (if ts.isEmpty then some none else none)
  let (_, _, lam) ← openAbstractMVarsResult tmpl
  unless lam.isLambda do return (if ts.isEmpty then some none else none)
  -- Assign the flex slot `?m t₁ … tₖ` from the template `fun p₁ … pₙ => body`, whose params
  -- are the spec's synthesis holes. Three cases by param count against the flex arity `k`:
  --   • `n = k`: the params are value inputs (a leaf's coupled value); bind them to the args.
  --   • `n > k`: the params are sub-programs (`a₁`, `a₂` of a sequencing rule); each becomes a
  --     fresh web metavariable, carried in the target's program position and decomposed in turn.
  --   • `n < k`: a leaf reached under accumulated continuation binders; its `n` inputs are the
  --     `n` most-recent outputs, so project the params onto the last `n` flex binders (the
  --     do-block's lexical threading), dropping the ancestors it does not read.
  let mut binderTys := #[]
  let mut lamBody := lam
  while lamBody.isLambda do
    binderTys := binderTys.push lamBody.bindingDomain!
    lamBody := lamBody.bindingBody!
  -- A bare slot whose template has only value params is bound directly by the matcher.
  let amHead := g.AProg.getAppFn
  let hasProg := binderTys.any (·.getForallBody.getAppFn == amHead)
  if ts.isEmpty && !hasProg then return some none
  if binderTys.size > ts.size then
    -- Sub-program params at a lower-arity slot (`a₁`, `a₂` of a sequencing rule): the slot's
    -- value binds each to a fresh web metavariable `?hᵢ`, which the rebuilt target carries in
    -- the program position. Applying the rule leaves each `?hᵢ` as the flex slot of a subgoal,
    -- decomposed in turn.
    let tsTypes ← ts.mapM fun t => Meta.inferType t
    let htys ← binderTys.mapM fun bty =>
      tsTypes.foldrM (init := bty) (fun t acc => mkArrow t acc)
    let hs ← htys.mapM fun hty => (Meta.mkFreshExprMVar (some hty) : MetaM Expr)
    let m ← Meta.withLocalDeclsD ((Array.range ts.size).map fun i => (`w, fun _ => pure tsTypes[i]!))
      fun ws => Meta.mkLambdaFVars ws (lamBody.instantiateRev (hs.map (mkAppN · ws)))
    mvarId.assign m
    let slot := lamBody.instantiateRev (hs.map (mkAppN · ts))
    let c ← instantiateMVars g.c
    let rhs := mkAppN g.head (g.args.set! 17 slot |>.set! 18 c)
    let_expr rel@Lean.Order.PartialOrder.rel carrier inst pre _ := ← goal.getType | return none
    return some (some (← setTargetRaw goal (mkApp4 rel carrier inst pre rhs)))
  let a ←
    if binderTys.size == ts.size then
      mvarId.assign lam
      pure (lam.beta ts)
    else
      -- Value params under accumulated continuation binders: project onto the last binders.
      let tsTypes ← ts.mapM fun t => Meta.inferType t
      Meta.withLocalDeclsD ((Array.range ts.size).map fun i => (`w, fun _ => pure tsTypes[i]!))
        fun ws => do
          let body := lamBody.instantiateRev (ws.extract (ws.size - binderTys.size) ws.size)
          let m ← Meta.mkLambdaFVars ws body
          mvarId.assign m
          pure (m.beta ts)
  -- The concrete slot gets the same once-per-leaf substitution as the values: rule
  -- application leaves an assigned metavariable node per bind in it, and the `hasMVar` flags
  -- of the whole prefix would defeat pruning in every later inspection.
  let c ← instantiateMVars g.c
  let rhs := mkAppN g.head (g.args.set! 17 a |>.set! 18 c)
  let_expr rel@Lean.Order.PartialOrder.rel carrier inst pre _ := ← goal.getType | return none
  return some (some (← setTargetRaw goal (mkApp4 rel carrier inst pre rhs)))

/-- Apply the registered rule `si` to a goal `pre ⊑ rwp γ a c Q E`. Returns the curried
precondition subgoals, or `none` (state rolled back) if the rule does not apply. -/
def applyRule (goal : MVarId) (g : RWPApp) (si : SpecInfo) : AscendM (Option (List MVarId)) := do
  commitWhenSome? do
    let some c ← cachedRule si g | return none
    let some goal? ← fixAbstractSlot? goal g c | return none
    let goal := goal?.getD goal
    let .goals ngs ← c.rule.apply goal | return none
    return some ngs

end Ascend
