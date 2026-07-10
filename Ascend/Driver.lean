import Ascend.Solve

/-!
# The worklist driver

A depth-first worklist over goals: `solve` decomposes each goal until no strategy applies, at
which point the goal is emitted as a VC (with a `⊤ ⊑ ·` wrapper stripped at the `Prop`
lattice, so VCs reach the user as bare propositions).
-/

open Lean Meta

namespace Ascend

/-- Emit `goal` as a VC, stripping a `(⊤ : Prop) ⊑ ·` wrapper. -/
def emitVC (goal : MVarId) : AscendM Unit := do
  let mut goal := goal
  let target ← instantiateMVars (← goal.getType)
  if let some (_, relArgs) := parseRel? target then
    if relArgs[0]!.isProp && relArgs[2]!.isAppOf ``Lean.Order.top then
      let x := relArgs[3]!
      let vc ← goal.withContext <| mkFreshExprSyntheticOpaqueMVar x
      goal.assign (mkApp2 (mkConst ``Lean.Order.top_le_prop) x vc)
      goal := vc.mvarId!
  goal.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs.push goal }

/-- Decompose `goal` to exhaustion, collecting VCs. -/
def work (goal : MVarId) : AscendM Unit := do
  let mut stack := #[goal]
  while let some goal := stack.back? do
    stack := stack.pop
    match ← solve goal with
    | .goals subgoals => stack := stack ++ subgoals.reverse
    | .stop (.noSpecFound c) => throwError "ascend: no spec found for program{indentExpr c}"
    | .stop _ => emitVC goal

/-- Run the engine on `goal`. Returns the VCs, tagged `vc1`, `vc2`, …. -/
def run (goal : MVarId) : AscendM (Array MVarId) := do
  work goal
  let vcs := (← get).vcs
  for h : i in [:vcs.size] do
    vcs[i].setTag (Name.mkSimple s!"vc{i + 1}")
  return vcs

end Ascend
