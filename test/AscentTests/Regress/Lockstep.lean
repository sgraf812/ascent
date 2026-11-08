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

theorem wrp_loop {βc βa : Type} {E : (Lbl → Lbl → CS → Prop) × EStack⟨⟩}
    (R : βc → CS → βa → Prop) (cinit : βc) (ainit : βa)
    {fc : Unit → βc → BlockM CS (ForInStep βc)} {fa : βa → BlockM (BitVec 64) (ForInStep βa)}
    {Q : βc → βa → CS → Prop}
    (hbody : ∀ c a, (fun t => R c t a) ⊑
      wrp (ofStateRepr view) (fc () c) (fa a) (fun rc ra t => match rc, ra with
        | .yield c', .yield a' => R c' t a'
        | .done c', .done a' => Q c' a' t
        | _, _ => False) E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view) (FixLoop.mk.forIn cinit fc)
      (FixLoop.mk.forIn ainit fun _ a => fa a) Q E :=
  wrp_forIn_lockstep R cinit ainit (fa := fun _ a => fa a) hbody

ascend_def lp (v : BitVec 64) : BlockM (BitVec 64) (BitVec 64) from
  ⦃fun t => PureRefinement t.r v True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] lp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  ascend [wrp_loop (fun (_ : Unit) (t : CS) (a : BitVec 64) => PureRefinement t.r a True Eq)]

example (v : BitVec 64) : lp v = FixLoop.mk.forIn v fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield 7)) := rfl

end Ascent.Blocks.Lockstep
