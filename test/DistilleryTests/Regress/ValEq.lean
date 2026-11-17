import DistilleryTests.Setup.Blocks
import Distillery.Refinement.Lockstep

/-!
# A given abstract value that differs from the computed one

The loop starts at the abstract value `v + 0`. The solver computes `v` for the register. The
solution meets `v + 0` by `PureRefinement.of_val_eq`, and the verification condition `v = v + 0`
goes to `grind`.
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.ValEq

attribute [local distill] wrp_bind

distill_def lp (v : BitVec 64) : BlockM (BitVec 64) (BitVec 64) from
  ⦃fun t => PureRefinement t.r v True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] lp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [wrp_forIn_lockstep (R := _) () (v + 0)]
  invariants
  · fun _ t a => PureRefinement t.r a True Eq
  with finish

example (v : BitVec 64) : lp v = FixLoop.mk.forIn (v + 0) fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield 7)) := rfl

end Distillery.Blocks.ValEq
