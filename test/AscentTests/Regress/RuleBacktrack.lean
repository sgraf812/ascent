import AscentTests.Setup.Blocks
import Ascent.Refinement.Lockstep

/-!
# A rule that fails after it assigned the holes of the goal

On the goal `PureRefinement (p + 1) ?av ?P (Idx p)`, the rule `base` binds its pattern variable to
`p + 1`, assigns `?av := 0` and `?P := True`, and then fails on the relation `Idx (p + 1)`. The
solver restores the metavariable context after a failed rule, so `succ` meets the holes unassigned.
-/

open Std.WP Lean.Order Ascent Ascent.Blocks
open Ascent.Concretization (ofStateRepr)

namespace Ascent.Blocks.RuleBacktrack

def Idx (p c : BitVec 64) (j : Nat) : Prop := c = p + BitVec.ofNat 64 j

@[ascend_pure high] theorem base {p : BitVec 64} : PureRefinement p 0 True (Idx p) := fun _ => by
  simp [Idx]

@[ascend_pure] theorem succ {p c : BitVec 64} {j : Nat} {P : Prop} (h : PureRefinement c j P (Idx p)) :
    PureRefinement (c + 1) (j + 1) P (Idx p) := fun hp => by
  have := h hp
  simp only [Idx] at *
  subst this
  simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

attribute [local ascend] wrp_bind

ascend_def lp (p : BitVec 64) : BlockM (BitVec 64) Nat from
  ⦃fun t => PureRefinement t.r 0 True (Idx p)⦄
    (FixLoop.mk.forIn () fun _ _ => do setC (p + 1); pure (ForInStep.yield ())) ⪯[ofStateRepr view] lp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_forIn_lockstep (R := _) () (0 : Nat)]
  invariants
  · fun _ t a => PureRefinement t.r a True (Idx p)

example (p : BitVec 64) : lp p = FixLoop.mk.forIn 0 fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => p + 1; pure (ForInStep.yield 1)) := rfl

end Ascent.Blocks.RuleBacktrack
