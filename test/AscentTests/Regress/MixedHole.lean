import AscentTests.Setup.Blocks
import Ascent.Refinement.Lockstep

/-!
# Holes applied to a closed argument and a variable, or to a pair of variables

The body of a `FixLoop` loop has the type `Unit → β → m (ForInStep β)`, so the abstract body is
the hole `?fa () a`, and a loop value of pair type is split into `?fa () (a₁, a₂)`. The run
rewrites such a hole to a hole applied to its free variables: the closed argument `()` of type
`Unit` is dropped, and the pair contributes its fields. A nested pair `(a₁, (a₂, a₃))` contributes
`a₁`, `a₂` and `a₃`, each through its chain of projections.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.MixedHole

attribute [local ascend] wrp_bind

ascend_def unitArg (v : BitVec 64) : BlockM (BitVec 64) (BitVec 64) from
  ⦃fun t => PureRefinement t.r v True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] unitArg
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep (fun (_ : Unit) (t : CS) (a : BitVec 64) => PureRefinement t.r a True Eq) () v]

example (v : BitVec 64) : unitArg v = FixLoop.mk.forIn v fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield 7)) := rfl

ascend_def pairArg (v : BitVec 64) : BlockM (BitVec 64) (BitVec 64 × BitVec 64) from
  ⦃fun t => PureRefinement t.r v True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] pairArg
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep (fun (_ : Unit) (t : CS) (a : BitVec 64 × BitVec 64) => match a with
    | (a₁, a₂) => PureRefinement t.r a₁ True Eq ∧ PureRefinement t.r a₂ True Eq) () (v, v)]

example (v : BitVec 64) : pairArg v = FixLoop.mk.forIn (v, v) fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield (7, 7))) := rfl

ascend_def nestedArg (v : BitVec 64) : BlockM (BitVec 64) (BitVec 64 × BitVec 64 × BitVec 64) from
  ⦃fun t => PureRefinement t.r v True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] nestedArg
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep (fun (_ : Unit) (t : CS) (a : BitVec 64 × BitVec 64 × BitVec 64) => match a with
    | (a₁, a₂, a₃) => PureRefinement t.r a₁ True Eq ∧ PureRefinement t.r a₂ True Eq ∧
        PureRefinement t.r a₃ True Eq) () (v, v, v)]

example (v : BitVec 64) : nestedArg v = FixLoop.mk.forIn (v, v, v) fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield (7, 7, 7))) := rfl

end Ascent.Blocks.MixedHole
