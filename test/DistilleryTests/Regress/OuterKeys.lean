import Distillery.PureRefinement
import Distillery.Tactic.VCGen.Command

/-!
# A compound entry over a parameter

The precondition `PureRefinement (c + c) d True Eq` abstracts the compound term `c + c` to `d`. The
parameter `c` is in scope of the abstract program, so the entry leaves `c` free for the
premise-free rule `abs_refl`, and the abstract program of `pure c` is `pure c`.
-/

open Std.WP Lean.Order Distillery

namespace OuterKeysTest

@[distill_pure low] theorem abs_refl {c : Nat} : PureRefinement c c True Eq :=
  PureRefinement.of_rel rfl

attribute [local distill] wrp_bind Refinement.pure_rel

def prog (c : Nat) : Demonic Nat := pure c

distill_def progA (c d : Nat) : Demonic Nat from
  ⦃(PureRefinement (c + c) d True Eq : Prop)⦄ (prog c) ⪯[Concretization.id Prop] progA ⦃(⌜Eq · ·⌝)⦄
  distill [prog]

/--
info: def OuterKeysTest.progA : Nat → Demonic Nat :=
fun c => do
  Demonic.assert True
  pure c
-/
#guard_msgs in
#print progA

end OuterKeysTest
