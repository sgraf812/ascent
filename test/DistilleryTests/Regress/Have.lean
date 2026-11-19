import DistilleryTests.Regress.Split

/-!
# A `have` of a pure value becomes a `have` of the abstract value

The program `progLet` binds `offset := v + 1` and uses `offset` twice. The run gives the abstract
program the binding `have offset := v + 1`, with the entry `PureRefinement offset offset' True Eq`,
and each use of `offset` becomes `offset'`. The program `progMut` updates a mutable variable in both
branches of an `if`, and the do-elaborator turns each update into a `have`: each branch of the
abstract program has its own `have`, and both branches jump to the abstract join point. The program
`progTwo` runs `progIf` twice, and `progIf` has no join point: both branches of the first `if`
reach the second `progIf`, and the second branch meets the abstract `if` that the first branch
synthesized, so the run abstracts the concrete condition to the given abstract one. In the first
branch, the state that the second `get` reads is the local `y` of a `have`, and the entry of the
second `get` takes precedence over the entry of the `have`. The test pins the deviation "pure refinements" of
`docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery SplitTest

namespace HaveTest

attribute [local distill] wrp_bind

@[distill_pure] theorem abs_add {a b x y : Nat} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

def progLet (v : Nat) : SM Nat Unit := do
  let s ← get
  let offset := v + 1
  set (s + offset)
  let s ← get
  set (s - offset)

distill_def progLetA (v : Nat) : SM Nat Unit from
  ⦃fun _ => True⦄ (progLet v) ⪯[γ Nat] progLetA ⦃fun _ _ _ => True⦄
  distill [progLet]

/--
info: def HaveTest.progLetA : Nat → SM Nat Unit :=
fun v => do
  let x ← get
  have offset : Nat := v + 1
  set (x + offset)
  let x ← get
  set (x - offset)
-/
#guard_msgs in
#print progLetA

def progMut (v : Nat) : SM Nat Unit := do
  let s ← get
  let mut x := s
  if 1 < x then x := x + v else x := x - v
  set x

distill_def progMutA (v : Nat) : SM Nat Unit from
  ⦃fun _ => True⦄ (progMut v) ⪯[γ Nat] progMutA ⦃fun _ _ _ => True⦄
  distill [progMut]

/--
info: def HaveTest.progMutA : Nat → SM Nat Unit :=
fun v => do
  let x ← get
  have __do_jp : PUnit → Nat → StateT Nat Demonic PUnit := fun x x_1 => set x_1
  if 1 < x then
      have x := x + v;
      __do_jp PUnit.unit x
    else
      have x := x - v;
      __do_jp PUnit.unit x
-/
#guard_msgs in
#print progMutA

def progIf (v : Nat) : SM Nat Unit := do
  let s ← get
  if 1 < s then
    let y := s + v
    set y
  else set s

def progTwo (v : Nat) : SM Nat Unit := do progIf v; progIf v

distill_def progTwoA (v : Nat) : SM Nat Unit from
  ⦃fun _ => True⦄ (progTwo v) ⪯[γ Nat] progTwoA ⦃fun _ _ _ => True⦄
  distill [progTwo, progIf]

/--
info: def HaveTest.progTwoA : Nat → SM Nat Unit :=
fun v => do
  do
    let x ← get
    if 1 < x then
        have y := x + v;
        set y
      else set x
  let x ← get
  if 1 < x then
      have y := x + v;
      set y
    else set x
-/
#guard_msgs in
#print progTwoA

end HaveTest
