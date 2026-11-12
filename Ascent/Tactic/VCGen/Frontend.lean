import Lean.Elab.Tactic.VCGen.Frontend
import Ascent.Tactic.VCGen.Driver

/-!
# The `ascend` tactic

`ascend` runs the forked worklist on a goal `⦃P⦄ c ⪯[γ] a ⦃Q; E⦄`. The `wrp` goals use the
`@[ascend]` database, and the `wp` goals use the `@[spec]` database. A natural metavariable in
`a` is a synthesis hole. `ascend [f, g]` unfolds the definitions `f` and `g` in both kinds of goals,
and takes any other term as a spec of the invocation. `ascend … with g` runs the `grind` step `g`
on every verification condition, as `vcgen … with g` does.
-/

open Lean Meta Elab Tactic Sym

namespace Lean.Elab.Tactic.VCGen.Ascend

open Lean.Elab.Tactic.VCGen.SpecAttr

register_option ascend.maxExponent : Nat := {
  defValue := 16
  descr := "the largest exponent `n` for which the `simp` step of `ascend` evaluates a power `a ^ n` \
    of literals"
}

syntax (name := ascendTac) "ascend" (" [" term,* "]")? (ppSpace Lean.Parser.Tactic.invariantAlts)?
  (" with " vcgenDischarge)? : tactic

/-- Unseal the abstract program hole of a `Refinement` goal, so that rule application can assign
it. Returns the hole. -/
def unsealAbstractHole (goal : MVarId) : MetaM (Option MVarId) := do
  let target := (← instantiateMVars (← goal.getType)).headBeta
  unless target.isAppOfArity ``Ascent.Refinement 22 do return none
  let .mvar mvarId := target.getAppArgs[14]!.getAppFn | return none
  if (← mvarId.getDecl).kind matches .syntheticOpaque then
    mvarId.setKind .natural
  return some mvarId

/-- Replace the delayed assignment of each hole in `e` by an ordinary one: `?h xs := ?b` becomes
`?h := fun xs => b`, where `b` is the value of `?b`. An unapplied occurrence of `?h`, such as the
continuation of a bind, needs the ordinary assignment. The walk follows the raw assignment of each
metavariable and resolves the innermost hole first, so that each pending value is instantiated once
and every outer abstraction skips the closed lambdas below it. -/
partial def resolveDelayedHoles (e : Expr) : MetaM Unit := do
  let _ ← go e |>.run {}
where
  go (e : Expr) : StateRefT (Std.HashSet MVarId) MetaM Unit := do
    for mv in (e.collectMVars {}).result do
      if (← get).contains mv then continue
      modify (·.insert mv)
      if let some v ← getExprMVarAssignment? mv then
        go v
      else if let some d ← getDelayedMVarAssignment? mv then
        go (mkMVar d.mvarIdPending)
        let b ← instantiateMVars (mkMVar d.mvarIdPending)
        let val ← withLCtx' (← d.mvarIdPending.getDecl).lctx (mkLambdaFVars d.fvars b)
        modifyMCtx fun mctx => { mctx with dAssignment := mctx.dAssignment.erase mv }
        mv.assign val

/-- Restore the local context of the hole, and check that the synthesized program uses only the
free variables of that context. The unassigned metavariables of the program, which the run
emitted as sealed goals, take the same context. -/
def checkHoleScope (hole : MVarId) (decl : MetavarDecl) : MetaM Unit := do
  resolveDelayedHoles (mkMVar hole)
  let restore (mv : MVarId) := modifyMCtx (·.modifyExprMVarDecl mv fun d =>
    { d with lctx := decl.lctx, localInstances := decl.localInstances })
  restore hole
  let val ← instantiateMVars (mkMVar hole)
  let outOfScope (e : Expr) := (e.find? fun e => e.isFVar && !decl.lctx.contains e.fvarId!).isSome
  if outOfScope val then
    throwError "ascend: the synthesized abstract program mentions a variable that the run \
      introduced, such as the concrete state:{indentExpr val}"
  for mv in ← getMVars val do
    if outOfScope (← instantiateMVars (← mv.getType)) then
      throwError "ascend: a hole of the synthesized abstract program has a type that mentions a \
        variable that the run introduced"
    restore mv

/-- Close every table of the synthesized program: the chain `(k₁, b₁) :: … :: ?rest` that the run
built one cell per key ends with `?rest := []`. -/
def closeTables (hole : MVarId) : MetaM Unit := do
  for mv in ← getMVars (← instantiateMVars (mkMVar hole)) do
    let ty ← instantiateMVars (← mv.getType)
    if ty.isAppOfArity ``Ascent.Table 2 then
      let #[κ, β] := ty.getAppArgs | continue
      mv.assign (mkApp (mkConst ``List.nil [0]) (mkApp2 (mkConst ``Prod [0, 0]) κ β))
    else if ty.isAppOfArity ``List 1 && ty.appArg!.isAppOfArity ``Prod 2 then
      mv.assign (mkApp (mkConst ``List.nil [0]) ty.appArg!)

/-- A spec passed at the invocation, `ascend [t]`: the proof `t` with its metavariables abstracted,
in `pre ⊑ wrp …` form, at the priority of core's explicit specs, above the unfold equations. For a
`Refinement` theorem `t`, also the backward rule of `t` itself, for `Refinement` premises. -/
def mkSpecTheoremFromTerm (term : Syntax) : TacticM (SpecTheorem × Option BackwardRule) := withRef term do
  let e ← Tactic.elabTerm term none (mayPostpone := true)
  Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
  let e ← instantiateMVars e
  let isRefinement ← forallTelescope (← inferType e) fun _ body => do
    return (← whnfR body).isAppOf ``Ascent.Refinement
  let rule? ← if isRefinement then
      let r ← abstractMVars e
      pure (some (← Sym.mkBackwardRuleFromExpr r.expr r.paramNames.toList))
    else pure none
  let e ← if isRefinement then
      forallTelescope (← inferType e) fun xs _ => do
        mkLambdaFVars xs (← mkAppM ``Ascent.Refinement.le_wrp #[mkAppN e xs])
    else pure e
  let r ← abstractMVars e
  let (pattern, _) ← Sym.mkPatternFromExprWithKey r.expr r.paramNames.toList fun type => do
    let some prog ← selectProg (← whnfR type)
      | throwError "ascend: the conclusion of {term} is not `pre ⊑ wrp …`:{indentExpr type}"
    return (prog, ())
  let id ← mkFreshId
  let spec : SpecTheorem :=
    { pattern := eraseUnusedVarsFromPattern pattern
      proof := .stx id term r.expr
      kind := .triple
      conjunctivePre := true
      priority := explicitSpecPrio }
  return (spec, rule?)

/-- The unfold equations of the definitions `declNames`, added to the spec database `specs`. -/
def addUnfoldSpecs (specs : SpecTheorems) (declNames : Array Name) : MetaM SpecTheorems := do
  let mut simpThms : SimpTheorems := {}
  for declName in declNames do
    simpThms ← simpThms.addDeclToUnfold declName
  addSimpSpecs specs simpThms

open Lean.Parser.Tactic in
def parseInvariantMap (stx : Syntax) :
    TermElabM (Option (Std.HashMap Nat Syntax)) := do
  let some altsStx := stx.getOptional? | return none
  let stx' : TSyntax ``invariantAlts := ⟨altsStx⟩
  match stx' with
  | `(invariantAlts| $_invariantsKW $alts*) =>
    if alts.isEmpty then return some {}
    let mut map : Std.HashMap Nat Syntax := {}
    let mut dotOrCase := LBool.undef
    for h : i in 0...alts.size do
      let alt := alts[i]
      match alt with
      | `(invariantDotAlt| · $_rhs) =>
        if dotOrCase matches .false then
          throwErrorAt alt "Alternation between labelled and bulleted invariants is not supported."
        dotOrCase := .true
        map := map.insert (i + 1) alt
      | `(invariantCaseAlt| | $tag $_args* => $_rhs) =>
        if dotOrCase matches .true then
          throwErrorAt alt "Alternation between labelled and bulleted invariants is not supported."
        dotOrCase := .false
        let n? : Option Nat := do
          let `(binderIdent| $tag:ident) := tag | some (i + 1) -- positional fallback
          let .str .anonymous s := tag.getId | none
          s.dropPrefix? "inv" >>= String.Slice.toNat?
        let some n := n? | throwErrorAt tag s!"Could not parse invariant label; expected `inv<n>`."
        if map.contains n then
          throwErrorAt tag s!"Duplicate invariant alternative for `inv{n}`."
        map := map.insert n alt
      | _ => throwErrorAt alt "Expected `invariantDotAlt` or `invariantCaseAlt`."
    return some map
  | _ => return none

def elabRemainingInvariants (alts : Std.HashMap Nat Syntax)
    (invariants : Array MVarId) (inlineHandled : Std.HashSet Nat) : SymM Unit := do
  let mut handled := inlineHandled
  for h : i in 0...invariants.size do
    let n := i + 1
    if handled.contains n then continue
    let some alt := alts[n]? | continue
    handled := handled.insert n
    discard <| elabInvariant alts n invariants[i]
  for (n, alt) in alts.toArray do
    unless handled.contains n do
      logWarningAt alt s!"Invariant alternative `inv{n}` does not match any invariant goal."

@[tactic ascendTac]
def elabAscend : Tactic := fun stx => withMainContext do
  -- An identifier of a definition is unfolded; any other term is a spec of this invocation.
  let mut declNames := #[]
  let mut termSpecs := #[]
  for arg in stx[1][1].getSepArgs do
    if arg.isIdent then
      if let some declName ← observing? (realizeGlobalConstNoOverloadWithInfo arg) then
        if let some (.defnInfo _) := (← getEnv).find? declName then
          declNames := declNames.push declName
          continue
    termSpecs := termSpecs.push arg
  let goal ← getMainGoal
  let hole? ← unsealAbstractHole goal
  let holeDecl? ← hole?.mapM (·.getDecl)
  let thms ← vcgenSimpExt.getTheorems
  let simpMethods : Sym.Simp.Methods :=
    { pre := Sym.Simp.beta >> Sym.Simp.reduceProj >> Sym.Simp.reduceMatcher
      post := Sym.Simp.evalGround { maxExponent := ascend.maxExponent.get (← getOptions) } >>
        thms.rewrite }
  -- The `with` clause is a `grind` step, as for `vcgen`.
  let mut step? : Option (TSyntax `grind) := none
  let invariantAlts? ← parseInvariantMap stx[2]
  if stx[3].getNumArgs == 2 then
    let w := stx[3][1]
    if w.getKind == ``Lean.Parser.Tactic.vcgenDischargeGrind then step? := some ⟨w[0]⟩
    else throwErrorAt w "`ascend … with` expects a `grind`-mode discharging step, not a general tactic"
  -- Hypotheses are internalized only for a `with` step that reads the E-graph, as for `vcgen`.
  let ctx : Context :=
    { backwardRules := ← mkBackwardRules, rintros := ← getRIntros, simpMethods, internalize := step?.isSome,
      invariantAlts := invariantAlts?.getD {} }
  let mut specs ← addUnfoldSpecs (← getAscendSpecTheorems) declNames
  let mut refinementRules := #[]
  for term in termSpecs do
    let (spec, rule?) ← mkSpecTheoremFromTerm term
    specs := specs.insert spec
    if let some rule := rule? then refinementRules := refinementRules.push rule
  let scope : Scope := { specs }
  let coreScope : Scope := { specs := ← addUnfoldSpecs (← getSpecTheorems) declNames }
  let params ← Grind.mkDefaultParams { clean := false }
  let (_, state) ← Grind.GrindTacticM.runAtGoal goal params (sym := true) do
    let g ← Lean.Elab.Tactic.Grind.getMainGoal
    let result ← Lean.Elab.Tactic.Grind.liftGrindM do
      if let some decl := holeDecl? then
        pureEnvExt.modifyState fun env =>
          { env with outer := decl.lctx.foldl (fun xs d => xs.insert d.fvarId) {} }
      refinementSpecsExt.modifyState fun _ => refinementRules
      let result ← run g ctx scope coreScope
      if let some alts := invariantAlts? then
        elabRemainingInvariants alts result.invariants result.inlineHandledInvariants
      return result
    let invariants ← result.invariants.filterM (not <$> ·.isAssigned)
    let invGoals ← Lean.Elab.Tactic.Grind.liftGrindM <| invariants.toList.mapM Grind.mkGoalCore
    Lean.Elab.Tactic.Grind.replaceMainGoal (invGoals ++ result.vcs.toList)
    -- The step runs on every verification condition, as `vcgen … <;> g` does.
    if let some step := step? then
      let mut rest := []
      for vc in ← Lean.Elab.Tactic.Grind.getUnsolvedGoals do
        Lean.Elab.Tactic.Grind.setGoals [vc]
        Lean.Elab.Tactic.Grind.evalGrindTactic step
        rest := rest ++ (← Lean.Elab.Tactic.Grind.getUnsolvedGoals)
      Lean.Elab.Tactic.Grind.setGoals rest
  if let (some hole, some decl) := (hole?, holeDecl?) then
    checkHoleScope hole decl
    closeTables hole
  replaceMainGoal (state.goals.map (·.mvarId))

end Lean.Elab.Tactic.VCGen.Ascend
