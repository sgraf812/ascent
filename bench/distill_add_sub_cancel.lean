import Driver
import Cases.AddSubCancel

/-! # `AddSubCancel`, engine measurements

The `vcgen` sizes are `[200, 1200, 2200]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.AddSubCancel

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (loop $(quote n)) ⪯[γ Nat] (?_ : SM Nat Unit) ⦃fun _ _ _ => True⦄)
  expected? := some (← `(loop $(quote n))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "AddSubCancel" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [30, 60, 90]
