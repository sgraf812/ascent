import DistilleryTests.Regress.Split

/-!
# A join point becomes an abstract join point

The program `steps` updates a mutable variable `x` in both branches of three consecutive `if`s,
and the do-elaborator shares the code after each `if` through a join point `__do_jp`. The run gives
the abstract program one join point for each concrete join point. Each jump `__do_jp () x` becomes
the jump `__do_jp () x'` to the abstract join point, where `x'` is the abstract value of the
argument `x`, and the run distills the code of each join point once: the abstract program has one
`set` and six jumps, where the inlined join points give eight `set`s. The test pins the deviation
"pure refinements" of `docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery SplitTest

namespace JoinPointTest

attribute [local distill] wrp_bind

@[local distill_pure] theorem abs_add {a b x y : Nat} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

def steps (v : Nat) : SM Nat Unit := do
  let s ← get
  let mut x := s
  if 0 < x then x := x + v else x := x - v
  if 1 < x then x := x + v else x := x - v
  if 2 < x then x := x + v else x := x - v
  set x

distill_def stepsA (v : Nat) : SM Nat Unit from
  ⦃fun _ => True⦄ (steps v) ⪯[γ Nat] stepsA ⦃fun _ _ _ => True⦄
  distill [steps]

/--
info: def JoinPointTest.stepsA : Nat → SM Nat Unit :=
fun v => do
  let x ← get
  have __do_jp : PUnit → Nat → StateT Nat Demonic PUnit := fun x x_1 =>
    have __do_jp := fun x x_2 =>
      have __do_jp := fun x x_3 => set x_3;
      if 2 < x_2 then
        have x := x_2 + v;
        __do_jp PUnit.unit x
      else
        have x := x_2 - v;
        __do_jp PUnit.unit x;
    if 1 < x_1 then
      have x := x_1 + v;
      __do_jp PUnit.unit x
    else
      have x := x_1 - v;
      __do_jp PUnit.unit x
  if 0 < x then
      have x := x + v;
      __do_jp PUnit.unit x
    else
      have x := x - v;
      __do_jp PUnit.unit x
-/
#guard_msgs in
#print stepsA

end JoinPointTest
