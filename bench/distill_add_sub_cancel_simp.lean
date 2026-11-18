import Driver
import Cases.AddSubCancelSimp

/-! # `AddSubCancelSimp`, engine measurements

The `vcgen` sizes are `[100, 400, 700]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.AddSubCancelSimp

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (loop $(quote n)) ⪯[γ Nat] (?_ : SM Nat Unit) ⦃fun _ _ _ => True⦄)
  expected? := some (← `(loop $(quote n))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "AddSubCancelSimp" mk [``loop, ``step] `(tactic| distill [wrp_get_SM, wrp_set_SM, wrp_pure_unit_SM])
  `(tactic| grind) [30, 60, 90]
