import Driver
import Cases.Catch

/-! # `Catch`, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.Catch

def mk (n : Nat) : MetaM Problem := return {
  stmt := ← `(⦃(⊤ : Prop)⦄ (catchN $(quote n) 0) ⪯[γe] (?_ : Except Nat Nat)
    ⦃fun c a => ⌜c = a⌝; (fun ec ea => ⌜ec = ea⌝)⦄)
  expected? := some (← `(catchN $(quote n) 0)) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "Catch" mk [``catchN] `(tactic| distill) `(tactic| grind) [250, 500, 750]
