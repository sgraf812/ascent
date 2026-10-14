import Ascend.Driver

/-!
# The `ascend` tactic

On a goal `⦃P⦄ c ⪯[γ] ?a ⦃Q; E⦄`, synthesizes the abstract program into `?a` while proving
the triple, leaving the verification conditions as goals. A statement hole elaborates to a
sealed (synthetic opaque) metavariable, which rule application would treat as rigid; the
frontend unseals it. With a concrete abstract program the same engine checks the refinement.
-/

open Lean Meta Sym Elab

namespace Ascend

/-- Unseal the abstract-program hole of a `Refinement` goal so rule application can assign it. -/
def unsealAbstractHole (goal : MVarId) : MetaM Unit := do
  let target ← goal.getType
  unless target.isAppOfArity ``Ascent.Refinement 22 do return
  let a := target.getAppArgs[14]!
  let .mvar mvarId := a.getAppFn | return
  if (← mvarId.getDecl).kind matches .syntheticOpaque then
    mvarId.setKind .natural

open Lean.Elab.Tactic in
/-- Intern every backward rule's matching pattern, so apply-time unification is pointer-fast. -/
def shareCommonRules (br : VCGen.BackwardRules) : SymM VCGen.BackwardRules :=
  return { br with
    tripleIntro := ← br.tripleIntro.shareCommon
    stateArgIntro := ← br.stateArgIntro.shareCommon
    propPreIntro := ← br.propPreIntro.shareCommon
    ofPropPreIntro := ← br.ofPropPreIntro.shareCommon
    truePreIntro := ← br.truePreIntro.shareCommon
    elimPre := ← br.elimPre.shareCommon
    andIntro := ← br.andIntro.shareCommon
    refl := ← br.refl.shareCommon
    meetTop := ← br.meetTop.shareCommon
  }

/-- Run the engine on `goal`: unseal the abstract hole, decompose (unfolding the concrete
definitions in `unfold` first), and return the VCs. -/
def mainWith (goal : MVarId) (unfold : Array Name) : MetaM (Array MVarId) := do
  unsealAbstractHole goal
  let specs ← getSpecs
  let latticeOps := Lean.Elab.Tactic.VCGen.latticeOps
  let rawRules ← Lean.Elab.Tactic.VCGen.mkBackwardRules
  SymM.run do
    let ctx : Context := { specs, latticeOps, backwardRules := ← shareCommonRules rawRules }
    (run goal unfold).run ctx |>.run' {}

/-- Run the engine on an already-unfolded `goal`. -/
def main (goal : MVarId) : MetaM (Array MVarId) := mainWith goal #[]

@[inherit_doc main]
syntax (name := ascendTac) "ascend" : tactic

elab_rules : tactic
  | `(tactic| ascend) => do
    let vcs ← main (← Tactic.getMainGoal)
    Tactic.replaceMainGoal vcs.toList

end Ascend
