import Ascend.RuleConstruction
import Lean.Elab.Tactic.Do.Internal.VCGen.LatticeOp

/-!
# Lattice-connective decomposition

A residual precondition `pre ⊑ rhs` whose `rhs` is a `CompleteLattice` connective (`⊓`, `⇨`,
`⌜·⌝`, `⊤`) decomposes generically by the connective's saturation-and-terminal rule. The rule
construction is reused verbatim from `vcgen` (`mkLatticeOpRule`, carrier-generic over the
`Lean.Order` lattice), keyed by the operator head in the phase's `latticeOps` table; only the
`AscendM` dispatch is ours.
-/

open Lean Meta Sym
open Lean.Elab.Tactic.Do.Internal

namespace Ascend

/-- The lattice-split rule for the connective heading `rhs`, from the cache or built now (via the
reused `mkLatticeOpRule`) and interned. Keyed on the constant prefix and argument count, so every
`⊓`/`⇨`/`⌜·⌝`/`⊤` node of a chain shares one compiled rule. -/
def mkLatticeOpRuleCached (rhs : Expr) (op : VCGen.LatticeOp) : AscendM BackwardRule := do
  let key := (ExprPtr.mk (rhs.getAppPrefix op.numConst), rhs.getAppNumArgs)
  if let some rule := (← get).latticeCache[key]? then return rule
  let rule ← (← VCGen.mkLatticeOpRule rhs op).shareCommon
  modify fun s => { s with latticeCache := s.latticeCache.insert key rule }
  return rule

/-- Decompose a lattice connective on the right of `pre ⊑ rhs`: look the head up in the split
table, build (or reuse) its backward rule, and apply it. Returns the subgoals, or `none` when the
head is not a registered connective or its rule does not apply. -/
def splitLatticeOp? (goal : MVarId) (rhs : Expr) : AscendM (Option (List MVarId)) := do
  let some headName := rhs.getAppFn.constName? | return none
  let some op := (← read).latticeOps[headName]? | return none
  match ← (← mkLatticeOpRuleCached rhs op).apply goal with
  | .goals gs => return some gs
  | _ => return none

end Ascend
