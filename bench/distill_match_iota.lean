import Driver
import Cases.MatchIota

/-! # `MatchIota`, engine measurements

The `vcgen` sizes are `[500, 1000, 1500]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.MatchIota

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (loop $(quote n)) ⪯[γ Nat] (?_ : EM Nat Unit) ⦃fun _ _ _ => True; (fun e e' _ => e = e', estack⟨⟩)⦄)
  expected? := some (← `(loop $(quote n))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "MatchIota" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [20, 40, 60]
