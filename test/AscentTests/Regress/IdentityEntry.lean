import Ascent.PureRefinement
import Ascent.Tactic.VCGen.Command

/-!
# An environment entry with its own variable as abstract value

The precondition `PureRefinement c c True Eq` abstracts the variable `c` to itself. The solver
abstracts `c` by that entry, although the abstract value `c` is the `c` of an entry: the guard
against concrete variables in an abstract value applies to the premise-free `@[ascend_pure]` rules,
here `abs_refl`, and not to the entries of the environment.
-/

open Std.WP Lean.Order Ascent

namespace IdentityEntryTest

@[ascend_pure] theorem abs_add {a b x y : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure low] theorem abs_refl {c : Nat} : PureRefinement c c True Eq :=
  PureRefinement.of_rel rfl

attribute [local ascend] wrp_bind Refinement.pure_rel

def prog (c : Nat) : Demonic Nat := pure (c + 1)

ascend_def progA (c : Nat) : Demonic Nat from
  ⦃(PureRefinement c c True Eq : Prop)⦄ (prog c) ⪯[Concretization.id Prop] progA ⦃(⌜Eq · ·⌝)⦄
  ascend [prog]

/--
info: def IdentityEntryTest.progA : Nat → Demonic Nat :=
fun c => do
  Demonic.assume True
  pure (c + 1)
-/
#guard_msgs in
#print progA

end IdentityEntryTest
