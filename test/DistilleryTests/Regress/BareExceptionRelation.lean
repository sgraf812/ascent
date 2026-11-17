import Distillery.Refinement
import Distillery.Tactic.VCGen.Command

/-!
# A spec with a fixed bare exception relation

`Except Nat` has the bare exception postcondition `Nat → Prop`, so the exception relation of a
refinement between two `Except Nat` programs is the bare `Nat → Nat → Prop`. The spec `throw3` fixes
that relation to `fun ec ea => ec = ea`, and the goal asks for `fun ec ea => ec ≤ ea`. The rule
built from `throw3` weakens the spec's relation to the goal's with the VC `∀ ec ea, ec = ea → ec ≤ ea`,
which binds both exceptions. The test pins the deviation "rule construction for `wrp` specs" of
`docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery

namespace BareExceptionRelationTest

@[distill] theorem throw3 (ea : Nat) {Q : Nat → Nat → Prop} :
    ⦃(3 = ea : Prop)⦄ (MonadExceptOf.throw 3 : Except Nat Nat) ⪯[Concretization.id Prop]
      (MonadExceptOf.throw ea : Except Nat Nat) ⦃Q; fun ec ea => ec = ea⦄ :=
  (Refinement.throw 3 ea).weaken fun h => h

distill_def thrower : Except Nat Nat from
  ⦃(⊤ : Prop)⦄ (MonadExceptOf.throw 3 : Except Nat Nat) ⪯[Concretization.id Prop] thrower
    ⦃(⌜· = ·⌝); fun ec ea => ec ≤ ea⦄
  distill [] with finish

example : thrower = (MonadExceptOf.throw 3 : Except Nat Nat) := rfl

end BareExceptionRelationTest
