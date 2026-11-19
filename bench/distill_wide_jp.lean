import Driver
import Cases.WideJP

/-! # `WideJP`, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.WideJP

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (wide $(quote n)) ⪯[γ Nat] (?_ : SM Nat Nat) ⦃fun _ _ _ => True⦄) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "WideJP" mk [``wide, ``DistillBench.WideJP.chain] `(tactic| distill)
  `(tactic| grind) [30, 60, 90]
