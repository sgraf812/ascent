import Driver
import Cases.Backtrack

/-! # `Backtrack`, engine measurements

The size is the number `k` of candidates. The block has ten steps at every size. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.Blocks DistillBench.Backtrack
open Distillery.Concretization (ofStateRepr)

def mk (_ : Nat) : MetaM Problem := return {
  stmt := ← `(⦃fun _ => True⦄ (block 9) ⪯[ofStateRepr view] (?_ : BlockM (BitVec 64) Unit)
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄) }

def solve (k : Nat) (goal : MVarId) : MetaM (List MVarId) := do
  let specs ← (List.range k).toArray.mapM fun p => `(wrp_setC_idx $(quote p))
  solveUsingTactic goal (← `(tactic| distill [$specs,*]))

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runFamily "Backtrack" mk [``block] solve `(tactic| grind) [60, 120, 180]
