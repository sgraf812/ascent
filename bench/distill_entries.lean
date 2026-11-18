import Driver
import Cases.Entries

/-! # `Entries`, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.Blocks DistillBench.Entries
open Distillery.Concretization (ofStateRepr)

def mk (n : Nat) : MetaM Problem := do
  let vs := (List.range n).toArray.map fun i => mkIdent (Name.mkSimple s!"v{i}")
  let t := mkIdent `t
  let entries ← vs.zipIdx.mapM fun (v, i) => `(PureRefinement ($t $(quote i)) $v True Eq)
  let pre ← (entries.extract 1 n).foldlM (init := entries[0]!) fun acc e => `($acc ∧ $e)
  let reads ← (List.range n).toArray.mapM fun i => `($t $(quote i))
  let sum ← (reads.extract 1 n).foldlM (init := reads[0]!) fun acc r => `($acc + $r)
  let asum ← (vs.extract 1 n).foldlM (init := (vs[0]! : Term)) fun acc v => `($acc + $v)
  return {
    binders := #[← `(bracketedBinder| ($vs* : BitVec 64))]
    stmt := ← `(⦃fun $t => $pre⦄ (peek fun $t => $sum : BlockM RF (BitVec 64)) ⪯[ofStateRepr unitView]
      (?_ : BlockM Unit (BitVec 64)) ⦃fun c a _ => c = a; (fun l l' _ => l = l', estack⟨⟩)⦄)
    expected? := some (← `(pure $asum)) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "Entries" mk [] `(tactic| distill) `(tactic| grind) [30, 60, 90]
