import Distillery.Demonic.StateT
import Distillery.PureRefinement
import Distillery.Tactic.VCGen.Command

/-!
# A split on a value that the run reads from the state

The program reads the state into `s` and splits on `s` with an `if`, a dependent `if` and a
`match`. The run binds `s` to the abstract variable `x` of the abstract program, with the entry
`PureRefinement s x True Eq`. The value solver abstracts the condition `1 < s` to `1 < x` and the
discriminant `s` to `x`, so the abstract program splits on `x`, and the abstract `match` has one
alternative for each concrete alternative. The test pins the deviation "two-sided split" of
`docs/vcgen-fork.md`.
-/

open Std.WP Lean.Order Distillery

namespace StateSplitTest

abbrev SM (σ : Type) := StateT σ Demonic

abbrev γ (σ : Type) : Concretization (σ → Prop) (σ → Prop) := Concretization.id (σ → Prop)

section
variable {σ : Type}

theorem wp_get_SM (Q : σ → σ → Prop) (E : EStack⟨⟩) (s : σ) : wp (get : SM σ σ) Q E s = Q s s := rfl

theorem wp_set_SM (v : σ) (Q : PUnit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (set v : SM σ PUnit) Q E s = Q ⟨⟩ v := rfl

@[distill] theorem wrp_get_SM {Q : σ → σ → σ → Prop} {E : EStack⟨⟩} :
    (fun s => ∀ x, PureRefinement s x True Eq → Q s x s)
      ⊑ wrp (γ σ) (get : SM σ σ) (get : SM σ σ) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_get_SM] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨s, h.1 s (PureRefinement.of_rel rfl), h.2⟩

@[distill] theorem wrp_set_SM (v w : σ) {Q : PUnit → PUnit → σ → Prop} {E : EStack⟨⟩} :
    (fun _ => PureRefinement v w True Eq ∧ Q ⟨⟩ ⟨⟩ v)
      ⊑ wrp (γ σ) (set v : SM σ PUnit) (set w : SM σ PUnit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_set_SM] at h ⊢
  obtain ⟨⟨hv, hq⟩, ha⟩ := h
  cases (hv trivial : v = w)
  rw [Concretization.post_pi]
  exact ⟨⟨⟩, hq, ha⟩

end

@[distill_pure low] theorem abs_eq_refl {α : Type} {c : α} : PureRefinement c c True Eq := fun _ => rfl

@[distill_pure] theorem abs_lt {a b x y : Nat} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a < b) (x < y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

@[distill_pure] theorem abs_sub {a b x y : Nat} {P₁ P₂ : Prop} (h₁ : PureRefinement a x P₁ Eq)
    (h₂ : PureRefinement b y P₂ Eq) : PureRefinement (a - b) (x - y) (P₁ ∧ P₂) Eq :=
  fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

attribute [local distill] wrp_bind

def progIte : SM Nat Unit := do let s ← get; if 1 < s then set 0 else set s

distill_def progIteA : SM Nat Unit from
  ⦃fun _ => True⦄ progIte ⪯[γ Nat] progIteA ⦃fun _ _ _ => True⦄
  distill [progIte]

/--
info: def StateSplitTest.progIteA : SM Nat Unit :=
do
  let x ← get
  if 1 < x then set 0 else set x
-/
#guard_msgs in
#print progIteA

def progDite : SM Nat Unit := do let s ← get; if _ : 1 < s then set (s - 1) else set s

distill_def progDiteA : SM Nat Unit from
  ⦃fun _ => True⦄ progDite ⪯[γ Nat] progDiteA ⦃fun _ _ _ => True⦄
  distill [progDite]

/--
info: def StateSplitTest.progDiteA : SM Nat Unit :=
do
  let x ← get
  if h : 1 < x then set (x - 1) else set x
-/
#guard_msgs in
#print progDiteA

def progMatch : SM Nat Unit := do
  let s ← get
  match s with
  | 0 => set 1
  | n + 1 => set n

distill_def progMatchA : SM Nat Unit from
  ⦃fun _ => True⦄ progMatch ⪯[γ Nat] progMatchA ⦃fun _ _ _ => True⦄
  distill [progMatch]

/--
info: def StateSplitTest.progMatchA : SM Nat Unit :=
do
  let x ← get
  match x with
    | 0 => set 1
    | n.succ => set n
-/
#guard_msgs in
#print progMatchA

end StateSplitTest
