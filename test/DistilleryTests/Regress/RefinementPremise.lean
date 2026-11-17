import DistilleryTests.Setup.Blocks

/-!
# A `Refinement` premise closed by a `Refinement` spec

The rule `wrp_wrap` refines `wrap c` to `wrap a` from the premise `⦃P⦄ c ⪯ a ⦃Q; E⦄`, whose
precondition `P` and abstract program `a` are schematic. The engine closes the premise with the
spec `inner.refines` of the invocation, which assigns `a` and `P`.

The spec keeps its abstract program schematic, the deviation "schematic abstract program" of
`docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.RefinementPremise

def wrap {σ α : Type} (x : BlockM σ α) : BlockM σ α := x

theorem wrp_wrap {c : BlockM CS Unit} {a : BlockM (BitVec 64) Unit} {P : CS → Prop}
    {Q : Unit → Unit → CS → Prop} {E : (Lbl → Lbl → CS → Prop) × EStack⟨⟩}
    (hk : ⦃P⦄ c ⪯[ofStateRepr view] a ⦃Q; E⦄) :
    P ⊑ wrp (ofStateRepr view) (wrap c) (wrap a) Q E :=
  hk.le_wrp

distill_def inner (v : BitVec 64) : BlockM (BitVec 64) Unit from
  ⦃fun t => PureRefinement t.r v True Eq⦄ (setC 7) ⪯[ofStateRepr view] inner
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill []

distill_def outer (v : BitVec 64) : BlockM (BitVec 64) Unit from
  ⦃fun t => PureRefinement t.r v True Eq⦄ (wrap (setC 7)) ⪯[ofStateRepr view] outer
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [wrp_wrap, inner.refines]

example : outer = wrap inner := rfl

end Distillery.Blocks.RefinementPremise
