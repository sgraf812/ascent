import DistilleryTests.Regress.Split

/-!
# A join point becomes an abstract join point

The program `steps` updates a mutable variable `x` in both branches of three consecutive `if`s,
and the do-elaborator shares the code after each `if` through a join point `__do_jp`. The run gives
the abstract program one join point for each concrete join point. Each jump `__do_jp () x` becomes
the jump `__do_jp () x'` to the abstract join point, where `x'` is the abstract value of the
argument `x`, and the run distills the code of each join point once: the abstract program has one
`set` and six jumps, where the inlined join points give eight `set`s.

The program `wide` jumps to its join point after `pick x`, which returns one of three values. The
rule `wrp_pure_var` gives the continuation of `pick x` a variable for the result, so the three
results share one abstract continuation `have y' := r'; __do_jp () y'`. The first result
synthesizes it, and the other results meet it: a later result closes the jump with the abstract
jump that the first result synthesized, and substitutes the abstract `have` where its concrete
`have y := 3` is substituted. The test pins the deviation "synthesis holes" of
`docs/vcgen-fork.md`.
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

theorem wrp_pure_var {α : Type} (c a : α) {Q : α → α → Nat → Prop} {E : EStack⟨⟩} :
    (fun s => PureRefinement c a True Eq ∧ ∀ a', PureRefinement c a' True Eq → Q c a' s)
      ⊑ wrp (γ Nat) (pure c : SM Nat α) (pure a : SM Nat α) Q E :=
  fun s h => wrp_pure (Q := Q) (E := E) c a s (h.2 a h.1)

attribute [local distill] wrp_pure_var

@[local distill_pure] theorem abs_eq {α : Type} {a b x y : α} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a = b) (x = y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

def pick (x : Nat) : SM Nat Nat := if x = 0 then pure (x + 2) else if x = 1 then pure 3 else pure 1

def wide : SM Nat Nat := do
  let x ← get
  let mut y := 0
  if x < 2 then y ← pick x
  return y + 1

distill_def wideA : SM Nat Nat from
  ⦃fun _ => True⦄ wide ⪯[γ Nat] wideA ⦃fun _ _ _ => True⦄
  distill [wide, pick]

/--
info: def JoinPointTest.wideA : SM Nat Nat :=
do
  let x ← get
  have __do_jp : PUnit → Nat → StateT Nat Demonic Nat := fun x x_1 => pure (x_1 + 1)
  if x < 2 then do
      let x ← if x = 0 then pure (x + 2) else if x = 1 then pure 3 else pure 1
      have y : Nat := x
      __do_jp PUnit.unit y
    else __do_jp PUnit.unit 0
-/
#guard_msgs in
#print wideA

end JoinPointTest
