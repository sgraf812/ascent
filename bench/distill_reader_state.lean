import Driver
import Cases.ReaderState

/-! # `ReaderState`, engine measurements

The `vcgen` sizes are `[600, 1600, 2600]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.ReaderState

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ _ => True⦄ (loop $(quote n)) ⪯[γ] (?_ : RM Unit) ⦃fun _ _ _ _ => True⦄)
  expected? := some (← `(loop $(quote n))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "ReaderState" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [20, 40, 60]
