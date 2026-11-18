import Driver
import Cases.RegFile

/-! # `RegFile`, engine measurements

The `vcgen` sizes are `[128, 256, 384]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.RegFile

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (loop $(quote n)) ⪯[γ Regs] (?_ : SM Regs Unit) ⦃fun _ _ _ => True⦄)
  expected? := some (← `(loop $(quote n))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "RegFile" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [30, 60, 90]
