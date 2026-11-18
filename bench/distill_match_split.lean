import Driver
import Cases.MatchSplit

/-! # `MatchSplit`, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.State DistillBench.MatchSplit

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (loop $(quote n)) ⪯[γ Nat] (?_ : EM Nat Unit) ⦃fun _ _ _ => True; (fun e e' _ => e = e', estack⟨⟩)⦄) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "MatchSplit" mk [``loop, ``step] `(tactic| distill)
  `(tactic| grind) [60, 120, 180]
