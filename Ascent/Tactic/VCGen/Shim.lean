import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.Util
import Ascent.Refinement
import Ascent.Tactic.VCGen.WRPApp

/-!
# The `wrp` counterparts of the `vcgen` lemmas and helpers

The translation table substitutes each `vcgen` lemma by the lemma here with the same name stem.
Each lemma takes the 17 arguments of `wrp` before `c`, then `a`, then the arguments that its `wp`
counterpart takes after the program type prefix.

The `@[ascend]` attribute keys a spec `pre ⊑ wrp γ c a Q E` on its concrete program `c`.
-/

open Lean Meta Sym Std.WP Lean.Order Ascent

namespace Ascent

universe u v w w' x y z

section
variable {CProg : Type x} {AProg : Type y} {CVal AVal : Type z}
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

theorem wrp_mono_erel_le [Assertion ERels] (x : CProg) (post : CVal → AVal → CPred) (eposts eposts' : ERels)
    (h : eposts ⊑ eposts') {pre : CPred} (h' : pre ⊑ wrp γ x a post eposts) :
    pre ⊑ wrp γ x a post eposts' := by
  sorry

theorem wrp_mono_bot_le [Assertion ERels] (x : CProg) (post : CVal → AVal → CPred) (eposts : ERels)
    {pre : CPred} (h : pre ⊑ wrp γ x a post ⊥) :
    pre ⊑ wrp γ x a post eposts := by
  sorry

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

initialize ascendSpecExt : SpecExtension ← registerSimpleScopedEnvExtension { mkSpecExt with name := `ascendSpecMap }

initialize registerBuiltinAttribute {
  name := `ascend
  descr := "a `pre ⊑ wrp …` spec for the ascend fork of vcgen"
  add := fun declName stx kind => do
    let prio ← getAttrParamOptPrio stx[1]
    let thm ← MetaM.run' (mkSpecTheoremFromConst declName prio)
    ascendSpecExt.add thm kind
}

/-- The `@[ascend]` database in scope. -/
def getAscendSpecTheorems : CoreM SpecTheorems :=
  return ascendSpecExt.getState (← getEnv)

end Lean.Elab.Tactic.VCGen.Ascend
