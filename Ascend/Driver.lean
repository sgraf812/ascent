import Ascend.Solve

/-!
# The worklist driver

A depth-first worklist over goals: `solve` decomposes each goal until no strategy applies, at
which point the goal is emitted as a VC (with a `⊤ ⊑ ·` wrapper stripped at the `Prop`
lattice, so VCs reach the user as bare propositions).
-/

open Lean Meta Sym

namespace Ascend

/-- Emit `goal` as a VC, stripping a `(⊤ : Prop) ⊑ ·` wrapper. -/
def emitVC (goal : MVarId) : AscendM Unit := do
  let goal ← elimTopPre goal
  goal.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs.push goal }

/-- Decompose the preprocessed `goal` to exhaustion, collecting VCs. -/
def work (goal : MVarId) : AscendM Unit := do
  let mut stack := #[(goal, ({} : Scope))]
  while let some (goal, scope) := stack.back? do
    stack := stack.pop
    match ← solve scope goal with
    | .goals scope subgoals => stack := stack ++ subgoals.reverse.map (·, scope)
    | .stop (.noSpecFound c) => throwError "ascend: no spec found for program{indentExpr c}"
    | .stop _ => emitVC goal

/-- Rewrite the goal with the equational lemmas of `unfold`, exposing a concrete program given
by definition (the tactic assumes an already-unfolded goal; the command unfolds here). -/
def unfoldConcrete (goal : MVarId) (unfold : Array Name) : AscendM MVarId := do
  if unfold.isEmpty then return goal
  let eqns : Array (Option (Array Name)) ← unfold.mapM fun n => getEqnsFor? n
  let thms := eqns.flatMap fun o => o.getD #[]
  match ← Sym.simpGoal goal (← Sym.mkMethods thms) with
  | .goal goal => return goal
  | .noProgress => return goal
  | .closed => throwError "ascend: unfolding {unfold} closed the goal"

/-- Run the engine on `goal`, first preprocessing and unfolding the concrete definitions.
Returns the VCs, tagged `vc1`, `vc2`, …. -/
def run (goal : MVarId) (unfold : Array Name := #[]) : AscendM (Array MVarId) := do
  let goal ← unfoldConcrete (← preprocessMVar goal) unfold
  work goal
  let vcs := (← get).vcs
  for h : i in [:vcs.size] do
    vcs[i].setTag (Name.mkSimple s!"vc{i + 1}")
  return vcs

end Ascend
