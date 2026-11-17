import DistilleryTests.Setup.Blocks
import Distillery.Refinement.Lockstep

/-!
# A spec whose `PureRefinement` premise has no solution

Two specs apply to `setC 7`. The later one, `wrp_setC_idx`, asks for an abstraction of `7` under
the relation `Idx p`, and no rule abstracts `7` there. The engine passes over that spec and applies
`wrp_setC`.
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.SpecBacktrack

def Idx (p c : BitVec 64) (j : Nat) : Prop := c = p + BitVec.ofNat 64 j

theorem wrp_setC_idx {p v : BitVec 64} {j : Nat} {P : Prop} (_h : PureRefinement v j P (Idx p))
    {Q : Unit → Unit → CS → Prop} {E : (Lbl → Lbl → CS → Prop) × EStack⟨⟩} :
    (fun t => P ∧ Q () () ⟨v, t.zf⟩)
      ⊑ wrp (ofStateRepr view) (setC v) (modifyIf (fun _ => True) fun _ => v : BlockM (BitVec 64) Unit) Q E := by
  intro t ht
  exact wrp_setC (Q := Q) (E := E) v t ht.2

attribute [local distill] wrp_bind
attribute [local distill high] wrp_setC_idx

distill_def lp (p : BitVec 64) : BlockM (BitVec 64) (BitVec 64) from
  ⦃fun t => PureRefinement t.r p True Eq⦄
    (FixLoop.mk.forIn () fun _ _ => do setC 7; pure (ForInStep.yield ())) ⪯[ofStateRepr view] lp
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill [wrp_forIn_lockstep (R := _) () p]
  invariants
  · fun _ t a => PureRefinement t.r a True Eq

example (p : BitVec 64) : lp p = FixLoop.mk.forIn p fun _ _ =>
    (do modifyIf (fun _ => True) fun _ => 7; pure (ForInStep.yield 7)) := rfl

end Distillery.Blocks.SpecBacktrack
