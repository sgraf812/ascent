import AscentTests.Setup.Blocks
import Ascent.Refinement.Lockstep

/-!
# A given abstract value and a given precondition that both differ from the solution

The loop starts at the abstract value `v + 0`. The second conjunct of the invariant asks for
`PureRefinement (t.r - 1) (v + 0 - 1) True Eq`. The rule `sub` abstracts `t.r - 1` to `v - 1` under
the precondition `0 < v`. The solution meets the abstract value `v + 0 - 1` by
`PureRefinement.of_val_eq` and the precondition `True` by `PureRefinement.weaken_pre`, whose
abstract value is the one of the goal.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.WeakenPreValEq

@[ascend_pure] theorem sub {c x : BitVec 64} {P : Prop} (h : PureRefinement c x P Eq) :
    PureRefinement (c - 1) (x - 1) (P ∧ 0 < x) Eq := fun hp => by
  rw [h hp.1]

attribute [local ascend] wrp_bind

ascend_def lp (v : BitVec 64) : BlockM (BitVec 64) (BitVec 64) from
  ⦃fun t => PureRefinement t.r v True Eq ∧ 0 < v⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] lp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep (R := _) () (v + 0)]
  invariants
  · fun _ t a => PureRefinement t.r a True Eq ∧ PureRefinement (t.r - 1) (a - 1) True Eq ∧ 0 < a
  with finish

example (v : BitVec 64) : lp v = FixLoop.mk.forIn (v + 0) fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield 7)) := rfl

end Ascent.Blocks.WeakenPreValEq
