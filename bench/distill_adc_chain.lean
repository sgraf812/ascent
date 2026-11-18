import Driver
import Cases.AdcChain

/-! # `AdcChain`, engine measurements

The `vcgen` sizes are `[250, 500, 750]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.AdcChain

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (prog $(quote n)) ⪯[γ S] (?_ : SM S Unit) ⦃fun _ _ _ => True⦄)
  expected? := some (← `(prog $(quote n))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "AdcChain" mk [``prog, ``AdcChain.chain] `(tactic| distill)
  `(tactic| grind) [150, 300, 450]
