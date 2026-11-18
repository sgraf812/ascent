import Driver
import Cases.PurePrecond

/-! # `PurePrecond`, engine measurements

The `vcgen` sizes are `[400, 2400, 4400]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.PurePrecond

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun s => s = true⦄ (loop $(quote n)) ⪯[γ Bool] (?_ : SM Bool Unit) ⦃fun _ _ _ => True⦄)
  expected? := some (← `(loop $(quote n))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "PurePrecond" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [150, 300, 450]
