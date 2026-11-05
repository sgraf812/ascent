import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.Util
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateS
import Ascent.Refinement
import Ascent.Tactic.VCGen.WRPApp

/-!
# The `wrp` counterparts of the `vcgen` lemmas and helpers

The translation table substitutes each `vcgen` lemma by the lemma here with the same name stem.
Each lemma takes the 17 arguments of `wrp` before `c`, then `a`, then the arguments that its `wp`
counterpart takes after the program type prefix.

The `@[ascend]` attribute keys a spec `pre ⊑ wrp γ c a Q E` on its concrete program `c`.
-/

open Lean Meta Sym Sym.Internal Std.WP Lean.Order Ascent

namespace Ascent

universe u w w' u₁ u₂ u₃ u₄

section
variable {CProg : Type u₁} {AProg : Type u₂} {CVal : Type u₃} {AVal : Type u₄}
  {CPred APred : Type w} {CEPosts AEPosts : Type w'} {ERels : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [WP AProg AVal APred AEPosts]
  [EPostsConcretization CPred APred CEPosts AEPosts ERels]
  {γ : Concretization CPred APred} {a : AProg}

theorem himp_mono_right_of_le {l : Type w} [CompleteLattice l] {p q q' : l} (h : q ⊑ q') :
    p ⇨ q ⊑ p ⇨ q' :=
  (PreservesSup.upperAdjoint_spec (meet p) q _).mpr fun y hy =>
    (PreservesSup.upperAdjoint_spec (meet p) q' _).mp PartialOrder.rel_refl y
      (PartialOrder.rel_trans hy h)

theorem wrp_mono_post_le (x : CProg) (post post' : CVal → AVal → CPred) (eposts : ERels)
    (h : post ⊑ post') {pre : CPred} (h' : pre ⊑ wrp γ x a post eposts) :
    pre ⊑ wrp γ x a post' eposts := by
  refine PartialOrder.rel_trans h' (iInf_mono fun Qa => iInf_mono fun Ea => ?_)
  refine himp_mono_right_of_le (WP.wp_monotone_post (x := x) fun cv => ?_)
  refine iSup_le _ _ fun av => ?_
  refine PartialOrder.rel_trans ?_ (le_iSup (fun av' => post' cv av' ⊓ γ.pred (Qa av')) av)
  exact meet_mono_left (h cv av)

theorem wrp_le_wrp_of_eq {x y : CProg} (h : x = y) (post : CVal → AVal → CPred)
    (eposts : ERels) : wrp γ y a post eposts ⊑ wrp γ x a post eposts := by
  subst h; exact PartialOrder.rel_refl

end

end Ascent

namespace Lean.Elab.Tactic.VCGen.Ascend

open Lean.Elab.Tactic.VCGen Lean.Elab.Tactic.VCGen.SpecAttr

/-- Unfold `⦃P⦄ c ⪯[γ] a ⦃Q; E⦄` into the underlying entailment `P ⊑ wrp γ c a Q E`. -/
def unfoldRefinement (goal : MVarId) : VCGenM MVarId := do
  let rule ← mkBackwardRuleFromDecl ``Ascent.Refinement.intro
  let .goals [goal] ← rule.apply goal
    | throwError "Failed to unfold the Refinement target of {goal}"
  return goal

/-- Rewrite every hypothesis of `goal` with the simp step. A hypothesis lifted from a precondition,
such as a branch condition or a guard, reaches the verification condition as written, and a
finisher needs it in the normal form the simp step gives the target. -/
def simpHypotheses (goal : MVarId) : VCGenM MVarId := do
  let some methods := (← read).simpMethods | return goal
  let mut goal := goal
  -- From the last hypothesis backwards: a replacement reintroduces the hypotheses after it.
  for fvarId in (← goal.getDecl).lctx.getFVarIds.reverse do
    let some decl := (← goal.getDecl).lctx.find? fvarId | continue
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    unless ← goal.withContext (isProp type) do continue
    let (result, simpState') ←
      goal.withContext <| Sym.Simp.SimpM.run (Sym.Simp.simp type) methods {} (← get).simpState
    modify fun s => { s with simpState := simpState' }
    if let .step type' proof .. := result then
      let r ← goal.withContext <| goal.replaceLocalDecl fvarId type' proof
      goal := r.mvarId
  return goal

/-- Replace the abstract program of the goal `pre ⊑ wrp γ c a Q E s₁ … sₙ` by `b`. -/
def setAbs (goal : MVarId) (info : WRPApp) (b : Expr) : VCGenM MVarId := do
  let_expr PartialOrder.rel α inst pre _ := ← goal.getType
    | throwError "setAbs: the goal is not an entailment"
  let rhs ← mkAppNS info.head (info.args.set! 18 b ++ info.excessArgs)
  let target ← mkAppNS (← goal.getType).getAppFn #[α, inst, pre, rhs]
  let g ← mkFreshExprSyntheticOpaqueMVar (← shareCommon target) (← goal.getTag)
  goal.assign g
  return g.mvarId!

/-- The cell of a table slot `Table.get tbl k` at a closed key `k`. A table under construction is
a chain `(k₁, b₁) :: … :: ?rest` that ends in a natural metavariable: the cell of a key with an
entry, else a fresh cell `?b` of the current context, appended as `?rest := (k, ?b) :: ?rest'`.
The local context of the table comes with a fresh cell, so that the caller can check that the
synthesized cell uses only that context. `none` when the key is open, the slot is not a table
under construction, or the key has no entry and the chain ends in no metavariable. -/
def tableCell (get : Expr) : VCGenM (Option (Option LocalContext × Expr)) := do
  let args := get.getAppArgs
  let κ := args[0]!
  let β := args[1]!
  let k := args[5]!
  if k.hasFVar || k.hasMVar then return none
  let mut tbl ← instantiateMVarsS args[4]!
  repeat
    if let .mvar m := tbl then
      unless (← m.getKind) matches .natural do return none
      let decl ← m.getDecl
      let b ← shareCommon (← mkFreshExprMVar β)
      let rest ← shareCommon (← withLCtx decl.lctx decl.localInstances (mkFreshExprMVar decl.type))
      let prodTy ← mkAppNS (← mkConstS ``Prod [0, 0]) #[κ, β]
      let entry ← mkAppNS (← mkConstS ``Prod.mk [0, 0]) #[κ, β, k, b]
      m.assign (← mkAppNS (← mkConstS ``List.cons [0]) #[prodTy, entry, rest])
      return some (decl.lctx, b)
    let_expr List.cons _ entry rest := tbl | return none
    let_expr Prod.mk _ _ k' b := entry | return none
    if k' == k then return some (none, b)
    tbl := rest
  return none

/-- Split a target `∀ x ∈ a :: l, G x` into `G a` and `∀ x ∈ l, G x`, and close
`∀ x ∈ [], G x`. -/
def forallMemList? (goal : MVarId) (target : Expr) : VCGenM (Option (List MVarId)) := do
  let .forallE _ _ (.forallE _ dom _ _) _ := target | return none
  let_expr Membership.mem _ _ _ l _ := dom | return none
  let l ← instantiateMVarsS l
  -- `MVarId.apply`: the premise `p a` of the lemma is a higher-order pattern under the binder.
  let lemma ←
    if l.isAppOfArity ``List.cons 3 then pure ``Ascent.forall_mem_cons_intro
    else if l.isAppOfArity ``List.nil 1 then pure ``Ascent.forall_mem_nil_intro
    else return none
  let some gs ← (liftM (observing? (goal.apply (← mkConstWithFreshMVarLevels lemma))) : VCGenM _)
    | return none
  -- The element `a` sits under projections in `G a`; reduce them, so that the premise meets the
  -- run in reduced form.
  let methods : Sym.Simp.Methods :=
    { pre := Sym.Simp.beta >> Sym.Simp.reduceProj >> Sym.Simp.reduceMatcher
      post := Sym.Simp.evalGround {} }
  let mut gs' := []
  for g in gs do
    let g ← preprocessMVar g
    match ← Sym.simpGoal g methods with
    | .goal g' => gs' := gs' ++ [g']
    | .noProgress => gs' := gs' ++ [g]
    | .closed => pure ()
  return some gs'

/-- The concrete program of a spec conclusion `pre ⊑ wrp γ c a Q E`. -/
def selectProg (type : Expr) : MetaM (Option Expr) := do
  match_expr type with
  | PartialOrder.rel _α _inst _pre rhs =>
    if rhs.getAppFn.isConstOf ``Ascent.wrp then
      return rhs.getAppArgs[WRPApp.progIdx]?
    return none
  | _ => return none

/-- The spec theorem for the declaration `declName`, keyed on its concrete program. -/
def mkSpecTheoremFromConst (declName : Name) (prio : Nat) : MetaM SpecTheorem := do
  let info := (← getAsyncConstInfo declName).toConstantVal
  let (pattern, _) ← Sym.mkPatternFromDeclWithKey declName fun type => do
    let some prog ← selectProg (← whnfR type)
      | throwError "@[ascend]: the conclusion of {declName} is not `pre ⊑ wrp …`"
    return (prog, ())
  let _ := info
  return { pattern := eraseUnusedVarsFromPattern pattern, proof := .global declName,
           kind := .triple, conjunctivePre := true, priority := prio }

/-- The declaration that `@[ascend]` registers for `declName`. A spec in `Refinement` form gets the
auxiliary theorem `declName.le_wrp`, its `pre ⊑ wrp …` form, since the spec database reads only
entailments. -/
def wrpFormOf (declName : Name) : MetaM Name := do
  let info ← getConstInfo declName
  let isRefinement ← forallTelescope info.type fun _ body =>
    return body.isAppOfArity ``Ascent.Refinement 22
  unless isRefinement do return declName
  let auxName := declName ++ `le_wrp
  if (← getEnv).contains auxName then return auxName
  let us := info.levelParams.map mkLevelParam
  let (type, value) ← forallTelescope info.type fun xs _ => do
    let prf ← mkAppM ``Ascent.Refinement.le_wrp #[mkAppN (mkConst declName us) xs]
    return (← mkForallFVars xs (← inferType prf), ← mkLambdaFVars xs prf)
  addDecl <| .thmDecl { name := auxName, levelParams := info.levelParams, type, value }
  return auxName

initialize ascendSpecExt : SpecExtension ← registerSimpleScopedEnvExtension { mkSpecExt with name := `ascendSpecMap }

initialize registerBuiltinAttribute {
  name := `ascend
  descr := "a `pre ⊑ wrp …` spec for the ascend fork of vcgen"
  add := fun declName stx kind => do
    let prio ← getAttrParamOptPrio stx[1]
    let thm ← MetaM.run' do mkSpecTheoremFromConst (← wrpFormOf declName) prio
    ascendSpecExt.add thm kind
}

/-- The `@[ascend]` database in scope. -/
def getAscendSpecTheorems : CoreM SpecTheorems :=
  return ascendSpecExt.getState (← getEnv)

end Lean.Elab.Tactic.VCGen.Ascend
