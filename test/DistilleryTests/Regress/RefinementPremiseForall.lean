import DistilleryTests.Setup.Blocks

/-!
# A `Refinement` premise under a binder

The rule `wrp_wrapAll` refines `wrapAll c` to `wrapAll a` from the premise `∀ v, ⦃P⦄ c v ⪯ a v ⦃Q; E⦄`,
whose abstract program `a v` is a hole applied to the bound `v`. The engine closes the premise with
the spec `inner.refines` of the invocation, whose last binder matches `v`.
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.RefinementPremiseForall

def wrap {σ α : Type} (x : BlockM σ α) : BlockM σ α := x

def wrapAll {σ : Type} (x : BitVec 64 → BlockM σ Unit) : BlockM σ Unit := x 0

theorem wrp_wrapAll {c : BitVec 64 → BlockM CS Unit} {a : BitVec 64 → BlockM (BitVec 64) Unit}
    {P : CS → Prop} {Q : Unit → Unit → CS → Prop} {E : (Lbl → Lbl → CS → Prop) × EStack⟨⟩}
    (hk : ∀ v : BitVec 64, ⦃P⦄ (c v) ⪯[ofStateRepr view] (a v) ⦃Q; E⦄) :
    P ⊑ wrp (ofStateRepr view) (wrapAll c) (wrapAll a) Q E :=
  (hk 0).le_wrp

distill_def inner (v w : BitVec 64) : BlockM (BitVec 64) Unit from
  ⦃fun t => PureRefinement t.r v True Eq⦄ (setC w) ⪯[ofStateRepr view] inner
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill []

distill_def outer (v : BitVec 64) : BlockM (BitVec 64) Unit from
  ⦃fun t => PureRefinement t.r v True Eq⦄ (wrapAll fun w => setC w) ⪯[ofStateRepr view] outer
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [wrp_wrapAll, inner.refines]

end Distillery.Blocks.RefinementPremiseForall
