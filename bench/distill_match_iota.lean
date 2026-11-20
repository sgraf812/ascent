import Driver
import Cases.MatchIota

/-! # `MatchIota`, engine measurements

The `vcgen` sizes are `[500, 1000, 1500]`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.MatchIota

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun s => s = 0⦄ (loop $(quote n)) ⪯[γ Nat] (?_ : EM Nat Unit) ⦃fun _ _ _ => True; (fun e e' _ => e = e', estack⟨⟩)⦄) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "MatchIota" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [20, 40, 60]
