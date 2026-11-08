import AscentTests.Setup.Blocks
import Ascent.Refinement.Lockstep

/-!
# A lockstep loop whose step relation is a `match`

Regression for `113749a`. The body post of `wrp_forIn_lockstep` is a `match` on the two loop
steps. At the `yield` leaf the post applies to two constructors; core's `instantiateGoal?` reduces
the `match`, and the `PureRefinement` solver assigns the abstract loop value.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.Lockstep

attribute [local ascend] wrp_bind

ascend_def lp (v : BitVec 64) : BlockM (BitVec 64) (BitVec 64) from
  ⦃fun t => PureRefinement t.r v True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] lp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep (fun (_ : Unit) (t : CS) (a : BitVec 64) => PureRefinement t.r a True Eq) () v]

example (v : BitVec 64) : lp v = FixLoop.mk.forIn v fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield 7)) := rfl

end Ascent.Blocks.Lockstep
