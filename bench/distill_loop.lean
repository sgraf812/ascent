import Driver
import Cases.Loop

/-! # `Loop`, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench DistillBench.Blocks DistillBench.Loop
open Distillery.Concretization (ofStateRepr)

def mk (n : Nat) : MetaM Problem := return {
  binders := #[← `(bracketedBinder| (v : BitVec 64))]
  stmt := ← `(⦃fun t => PureRefinement t.r v True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do body $(quote n); pure (ForInStep.yield ()))
      ⪯[ofStateRepr view] (?_ : BlockM (BitVec 64) (BitVec 64))
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄)
  expected? := some (← `(FixLoop.mk.forIn v fun _ _ =>
    (do bodyA $(quote n); pure (ForInStep.yield (BitVec.ofNat 64 0)) : BlockM (BitVec 64) _))) }

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runTactic "Loop" mk [``body] `(tactic| distill [wrp_forIn_lockstep (R := _) () v]
    invariants
    · fun _ t a => PureRefinement t.r a True Eq)
  `(tactic| grind) [240, 480, 720]
