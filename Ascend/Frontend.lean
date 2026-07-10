import Ascend.Driver

/-!
# The `ascend` tactic

On a goal `⦃P⦄ ?a ⊑[γ] c ⦃Q; E⦄`, synthesizes the abstract program into `?a` while proving
the triple, leaving the verification conditions as goals. A statement hole elaborates to a
sealed (synthetic opaque) metavariable, which rule application would treat as rigid; the
frontend unseals it. With a concrete abstract program the same engine checks the refinement.
-/

open Lean Meta Elab

namespace Ascend

/-- Unseal the abstract-program hole of an `RTriple` goal so rule application can assign it. -/
def unsealAbstractHole (goal : MVarId) : MetaM Unit := do
  let target ← goal.getType
  unless target.isAppOfArity ``Ascent.RTriple 22 do return
  let a := target.getAppArgs[13]!
  let .mvar mvarId := a.getAppFn | return
  if (← mvarId.getDecl).kind matches .syntheticOpaque then
    mvarId.setKind .natural

/-- Run the engine on `goal`: unseal the abstract hole, decompose, return the VCs. -/
def main (goal : MVarId) : MetaM (Array MVarId) := do
  unsealAbstractHole goal
  let ctx : Context := { specs := ← getSpecs }
  (run goal).run ctx |>.run' {}

@[inherit_doc main]
syntax (name := ascendTac) "ascend" : tactic

elab_rules : tactic
  | `(tactic| ascend) => do
    let vcs ← main (← Tactic.getMainGoal)
    Tactic.replaceMainGoal vcs.toList

end Ascend
