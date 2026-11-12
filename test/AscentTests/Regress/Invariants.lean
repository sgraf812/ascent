import AscentTests.Setup.Blocks
import Ascent.Refinement.Lockstep

/-!
# Loop invariants in an `invariants` section

The step relation `R` of `wrp_forIn_lockstep` has the invariant type `LockstepInvariant`. The
`invariants` section of `ascend_def` supplies it, one alternative per loop in program order.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.Invariants

attribute [local ascend] wrp_bind

ascend_def lp (v : BitVec 64) : BlockM (BitVec 64) (BitVec 64) from
  ⦃fun t => PureRefinement t.r v True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] lp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep (R := _) () v]
  invariants
  · fun _ t a => PureRefinement t.r a True Eq

example (v : BitVec 64) : lp v = FixLoop.mk.forIn v fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield 7)) := rfl

end Ascent.Blocks.Invariants
