import Driver
import Cases.Table

/-! # `Table`, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.Blocks DistillBench.Table
open Distillery.Concretization (ofStateRepr)

def mk (n : Nat) : MetaM Problem := do
  -- A list literal of 32 or more elements elaborates to `let` bindings, so the table is a chain
  -- of `List.cons`.
  let tbl ← (List.range n).foldrM (init := ← `(List.nil)) fun i rest =>
    `(List.cons ($(quote (i + 1)), cell) $rest)
  return {
    stmt := ← `(⦃fun _ => True⦄ (cells $tbl) ⪯[ofStateRepr view] (?_ : BlockM (BitVec 64) Unit)
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "Table" mk [] `(tactic| distill [wrp_cells (I := fun _ => True), cell])
  `(tactic| grind) [30, 60, 90]
