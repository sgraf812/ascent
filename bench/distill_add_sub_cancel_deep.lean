import Driver
import Cases.AddSubCancelDeep

/-! # `AddSubCancelDeep`, engine measurements

The `vcgen` sizes are `[100, 500, 900]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.AddSubCancelDeep

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ _ _ => True⦄ (loop $(quote n)) ⪯[γd] (?_ : DM Unit) ⦃fun _ _ _ _ _ => True⦄)
  expected? := some (← `(loop $(quote n))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 1024

#eval runTactic "AddSubCancelDeep" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [30, 60, 90]
