import DistilleryTests.Regress.Split

/-!
# Dead code after a `throw`, and entries of closed terms

The program `progThrow` in `EM := ExceptT String (StateT Nat Demonic)` throws inside the first
action of a bind, so the run never reaches the
continuation `pure 2`, and no rule assigns the hole of its abstract continuation. After the
worklist, the run distills the dead continuation in a goal whose proof it discards, so the abstract
program has the continuation as dead code.

The program `progClosed` runs under the precondition `s = 0`, so the state is the literal `0`. The
first block reads `0` into the abstract variable `x`, whose scope ends with the block. The later
`set 0` abstracts the closed term `0` by a rule: a closed term gives no entry, so the run does not
reuse `x` out of its scope. The test pins the deviations "one worklist" and "pure refinements" of
`docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery SplitTest

namespace DeadCodeTest

abbrev EM := ExceptT String (StateT Nat Demonic)

theorem wp_get_EM (Q : Nat → Nat → Prop) (E : (String → Nat → Prop) × EStack⟨⟩) (s : Nat) :
    wp (get : EM Nat) Q E s = Q s s := rfl

theorem wp_throw_EM {α : Type} (e : String) (Q : α → Nat → Prop)
    (E : (String → Nat → Prop) × EStack⟨⟩) (s : Nat) : wp (throw e : EM α) Q E s = E.1 e s := rfl

theorem wp_pure_EM {α : Type} (a : α) (Q : α → Nat → Prop)
    (E : (String → Nat → Prop) × EStack⟨⟩) (s : Nat) : wp (pure a : EM α) Q E s = Q a s := rfl

@[local distill] theorem wrp_get_EM {Q : Nat → Nat → Nat → Prop}
    {E : (String → String → Nat → Prop) × EStack⟨⟩} :
    (fun s => ∀ x, PureRefinement s x True Eq → Q s x s) ⊑ wrp (γ Nat) (get : EM Nat) (get : EM Nat) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_get_EM] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨s, h.1 s (PureRefinement.of_rel rfl), h.2⟩

@[local distill] theorem wrp_throw_EM {α : Type} (e : String) {Q : α → α → Nat → Prop}
    {E : (String → String → Nat → Prop) × EStack⟨⟩} :
    (fun s => E.1 e e s) ⊑ wrp (γ Nat) (throw e : EM α) (throw e : EM α) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_throw_EM] at h ⊢
  show (Concretization.id (Nat → Prop)).post E.1 Ea.1 e s
  rw [Concretization.post_pi]
  exact ⟨e, h.1, h.2⟩

@[local distill] theorem wrp_pure_EM {α : Type} (c a : α) {Q : α → α → Nat → Prop}
    {E : (String → String → Nat → Prop) × EStack⟨⟩} :
    (fun s => PureRefinement c a True Eq ∧ Q c a s) ⊑ wrp (γ Nat) (pure c : EM α) (pure a : EM α) Q E :=
  fun s h => wrp_pure (Q := Q) (E := E) c a s h.2

attribute [local distill] wrp_bind

def progThrow : EM Nat := do
  let _ ← (do let _ ← get; throw "e" : EM Nat)
  pure 2

distill_def progThrowA : EM Nat from
  ⦃fun _ => True⦄ progThrow ⪯[γ Nat] progThrowA ⦃fun _ _ _ => True; (fun e e' _ => e = e', estack⟨⟩)⦄
  distill [progThrow]

/--
info: def DeadCodeTest.progThrowA : EM Nat :=
do
  let _ ←
    do
      let _ ← get
      throw "e"
  pure 2
-/
#guard_msgs in
#print progThrowA

def progClosed : SM Nat Unit := do
  (do let s ← get; set s : SM Nat Unit)
  set 0

distill_def progClosedA : SM Nat Unit from
  ⦃fun s => s = 0⦄ progClosed ⪯[γ Nat] progClosedA ⦃fun _ _ _ => True⦄
  distill [progClosed]

/--
info: def DeadCodeTest.progClosedA : SM Nat Unit :=
do
  do
    let _ ← get
    set 0
  set 0
-/
#guard_msgs in
#print progClosedA

end DeadCodeTest
