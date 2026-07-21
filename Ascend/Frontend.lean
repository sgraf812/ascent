import Ascend.Driver

/-!
# The `ascend` tactic

On a goal `⦃P⦄ ?a ⊑[γ] c ⦃Q; E⦄`, synthesizes the abstract program into `?a` while proving
the triple, leaving the verification conditions as goals. A statement hole elaborates to a
sealed (synthetic opaque) metavariable, which rule application would treat as rigid; the
frontend unseals it. With a concrete abstract program the same engine checks the refinement.
-/

open Lean Meta Sym Elab

namespace Ascend

/-- Unseal the abstract-program hole of an `RTriple` goal so rule application can assign it. -/
def unsealAbstractHole (goal : MVarId) : MetaM Unit := do
  let target ← goal.getType
  unless target.isAppOfArity ``Ascent.RTriple 22 do return
  let a := target.getAppArgs[13]!
  let .mvar mvarId := a.getAppFn | return
  if (← mvarId.getDecl).kind matches .syntheticOpaque then
    mvarId.setKind .natural

open Lean.Elab.Tactic.Do.Internal in
/-- Intern every backward rule's matching pattern, so apply-time unification is pointer-fast. -/
def shareCommonRules (br : VCGen.BackwardRules) : SymM VCGen.BackwardRules :=
  return {
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
definitions in `unfold` first), return the VCs and the proof finalizer. Proof terms reference
the sub-program holes as fvars; the finalizer substitutes all of them at once with the
synthesized programs (one pass), and must be applied to the fully instantiated proof. -/
def mainWith (goal : MVarId) (unfold : Array Name) :
    MetaM (Array MVarId × (Expr → Expr)) := do
  unsealAbstractHole goal
  let specs ← getSpecs
  let latticeOps := Lean.Elab.Tactic.Do.Internal.VCGen.mkLatticeOpTable {}
  let rawRules ← Lean.Elab.Tactic.Do.Internal.VCGen.mkBackwardRules
  SymM.run do
    let act : AscendM (Array MVarId × (Expr → Expr)) := do
      let vcs ← run goal unfold
      let holes := (← get).holes
      -- The substituted programs are closed, so a direct pointer-cached replace suffices:
      -- unlike `replaceFVars` (abstract, then instantiate), it is binder-depth-independent
      -- and preserves the proof's sharing.
      let mut map : Std.HashMap FVarId Expr := {}
      for (f, m) in holes do
        map := map.insert f (← instantiateMVars (mkMVar m))
      let subst := map
      pure (vcs, fun e => e.replace fun x => match x with
        | .fvar id => subst[id]?
        | _ => none)
    let ctx : Context := { specs, latticeOps, backwardRules := ← shareCommonRules rawRules }
    act.run ctx |>.run' {}

/-- Run the engine on an already-unfolded `goal`, dropping the proof finalizer (usable only
when the program has no sequencing, so no sub-program holes arise). -/
def main (goal : MVarId) : MetaM (Array MVarId) := (·.1) <$> mainWith goal #[]

@[inherit_doc main]
syntax (name := ascendTac) "ascend" : tactic

elab_rules : tactic
  | `(tactic| ascend) => do
    let vcs ← main (← Tactic.getMainGoal)
    Tactic.replaceMainGoal vcs.toList

end Ascend
