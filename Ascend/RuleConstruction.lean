import Ascend.Context
import Ascend.Rules

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

/-- The hypothesis types of a curried `Prop`-lattice precondition: conjunctions split,
implication hypotheses distribute over their branch's hypotheses, leaves become entailments
`P' ⊑ leaf` (via `mkRel`). -/
private partial def curryHyps (mkRel : Expr → Expr) (pre : Expr) : List Expr :=
  if pre.isAppOfArity ``And 2 then
    curryHyps mkRel pre.appFn!.appArg! ++ curryHyps mkRel pre.appArg!
  else if pre.isArrow then
    curryHyps mkRel pre.bindingBody! |>.map fun t =>
      .forallE `a pre.bindingDomain! t .default
  else
    [mkRel pre]

/-- The proof of `P' ⊑ pre` from the curried hypotheses, consuming them in `curryHyps` order:
`prop_le_and` at conjunctions, `prop_le_imp` at implications (with the hypotheses applied to
the introduced antecedent), the hypothesis itself at a leaf. -/
private partial def buildPreProof (mkRel : Expr → Expr) (P' pre : Expr) (hyps : List Expr)
    (curried : Bool) : AscendM (Expr × List Expr) := do
  if curried && pre.isAppOfArity ``And 2 then
    let A := pre.appFn!.appArg!
    let B := pre.appArg!
    let (pa, rest) ← buildPreProof mkRel P' A hyps curried
    let (pb, rest) ← buildPreProof mkRel P' B rest curried
    return (mkApp5 (mkConst ``Ascend.prop_le_and) P' A B pa pb, rest)
  if curried && pre.isArrow then
    let A := pre.bindingDomain!
    let B := pre.bindingBody!
    -- Only this branch's hypotheses receive the antecedent; later siblings stay untouched.
    let n := (curryHyps id B).length
    let (own, rest) := (hyps.take n, hyps.drop n)
    let prf ← withLocalDeclD `a A fun a => do
      let (pb, leftover) ← buildPreProof mkRel P' B (own.map (mkApp · a)) curried
      unless leftover.isEmpty do throwError "ascend: precondition currying mismatch"
      mkLambdaFVars #[a] pb
    return (mkApp4 (mkConst ``Ascend.prop_le_imp) P' A B prf, rest)
  match hyps with
  | h :: rest => return (h, rest)
  | [] => throwError "ascend: precondition currying mismatch"

/-- Compile `spec` to apply-ready form against the phase of the goal `g`. -/
private def compileRule (si : SpecInfo) (g : RWPApp) : AscendM (Option CachedRule) := do
  let rule ← mkConstWithFreshMVarLevels si.declName
  -- Non-reducing: at the `Prop` lattice the `RTriple` conclusion would reduce to an
  -- implication and the telescope would consume the precondition as a binder.
  let (mvs, bis, concl) ← forallMetaTelescope (← Meta.inferType rule)
  let some (relTy, prf) ← conclusionProof rule mvs concl | return none
  let some ruleRwp := parseRWP? relTy | return none
  -- Pin the phase, and the monads (the proof-only instances depend on them).
  for i in phasePositions do
    unless ← isDefEqGuarded ruleRwp.args[i]! g.args[i]! do return none
  unless ← isDefEqGuarded ruleRwp.AProg.getAppFn g.AProg.getAppFn do return none
  unless ← isDefEqGuarded ruleRwp.CProg.getAppFn g.CProg.getAppFn do return none
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
  -- The auxiliary theorem `∀ P' h₁ … hₖ, P' ⊑ rwp …`, the precondition curried into the
  -- hypotheses `hᵢ`.
  let relTy ← instantiateMVars relTy
  let some rel := parseRel? relTy | return none
  let pre' ← instantiateMVars rel.pre
  let carrier ← instantiateMVars g.CPred
  let aux ← withLocalDeclD `P' carrier fun P' => do
    let mkRel := fun pre => mkApp4 rel.head rel.carrier rel.inst P' pre
    let hypTys := if carrier.isProp then curryHyps mkRel pre' else [mkRel pre']
    let decls := hypTys.toArray.map fun t => (`h, fun (_ : Array Expr) => (pure t : AscendM Expr))
    withLocalDeclsD decls fun hs => do
      let (prePrf, rest) ← buildPreProof mkRel P' pre' hs.toList (carrier.isProp)
      unless rest.isEmpty do throwError "ascend: precondition currying mismatch"
      let relTrans := mkConst ``Lean.Order.PartialOrder.rel_trans rel.head.constLevels!
      mkLambdaFVars (#[P'] ++ hs) <|
        mkApp7 relTrans rel.carrier rel.inst P' pre' rel.rhs prePrf (← instantiateMVars prf)
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
  if ts.isEmpty then return some none
  let some tmpl := c.template? | return none
  let (_, _, lam) ← openAbstractMVarsResult tmpl
  unless lam.isLambda do return none
  mvarId.assign lam
  let a := lam.beta ts
  -- The concrete slot gets the same once-per-leaf substitution as the values: rule
  -- application leaves an assigned metavariable node per bind in it, and the `hasMVar` flags
  -- of the whole prefix would defeat pruning in every later inspection.
  let c ← instantiateMVars g.c
  let rhs := mkAppN g.head (g.args.set! 17 a |>.set! 18 c)
  return some (some (← setTargetRaw goal (g.rel.rebuild rhs)))

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
