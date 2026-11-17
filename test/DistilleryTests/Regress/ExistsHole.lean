import DistilleryTests.Setup.Blocks

/-!
# An existential on the right side with a hole as witness

The step relation `∃ a, ra = a ∧ t.r ≐ a` names the abstract result through `∃`. The run
introduces the `∃` with a hole `?a`, assigns the abstract result `?r := ?a` from the equation, and
the value solver assigns `?a := r` from the entry `t.r ≐ r` of the precondition.
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.ExistsHole

attribute [local distill] wrp_pure

distill_def readR (r : BitVec 64) : BlockM (BitVec 64) (BitVec 64) from
  ⦃fun t => PureRefinement t.r r True Eq⦄ (pure () : BlockM CS Unit) ⪯[ofStateRepr view] readR
  ⦃fun _ ra t => ∃ a, ra = a ∧ PureRefinement t.r a True Eq; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill []

example (r : BitVec 64) : readR r = pure r := rfl

end Distillery.Blocks.ExistsHole
