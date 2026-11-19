import Driver
import Cases.IfsJP

/-! # `IfsJP`, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.IfsJP

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (loop $(quote n)) ⪯[γ Nat] (?_ : SM Nat Unit) ⦃fun _ _ _ => True⦄) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "IfsJP" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [5, 10, 15]
