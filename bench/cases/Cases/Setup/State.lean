import Distillery.Demonic.StateT
import Distillery.PureRefinement
import Distillery.Tactic.VCGen.Command

/-!
# State monads over `Demonic` under the identity concretization

The mirrors of the `vcgen` bench run in `SM σ := StateT σ Demonic` and in
`EM σ := ExceptT String (StateT σ Demonic)`. Each refinement relates a concrete program to an
abstract program in the same monad, under `Concretization.id`. The rules below map each concrete
step to the same abstract step. `wrp_get_SM` binds the state read to an abstract variable `x` of
the abstract program, with the entry `PureRefinement s x True Eq` for the value solver, and
`wrp_set_SM` asks the value solver for the abstract value of the written state. The case modules
register the rules that they use with `@[distill]`.
-/

open Std.WP Lean.Order Distillery

namespace DistillBench.State

abbrev SM (σ : Type) := StateT σ Demonic
abbrev EM (σ : Type) := ExceptT String (StateT σ Demonic)

abbrev γ (σ : Type) : Concretization (σ → Prop) (σ → Prop) := Concretization.id (σ → Prop)

/-- The exception relations of `EM σ`. -/
abbrev ER (σ : Type) := (String → String → σ → Prop) × EStack⟨⟩

/-- Throw `e` when `b` holds. -/
def throwIf {σ : Type} (b : Bool) (e : String) : EM σ Unit := if b then throw e else pure ()

section
variable {σ : Type}

theorem wp_get_SM (Q : σ → σ → Prop) (E : EStack⟨⟩) (s : σ) : wp (get : SM σ σ) Q E s = Q s s := rfl
theorem wp_set_SM (v : σ) (Q : PUnit → σ → Prop) (E : EStack⟨⟩) (s : σ) :
    wp (set v : SM σ PUnit) Q E s = Q ⟨⟩ v := rfl
theorem wp_get_EM (Q : σ → σ → Prop) (E : (String → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (get : EM σ σ) Q E s = Q s s := rfl
theorem wp_set_EM (v : σ) (Q : PUnit → σ → Prop) (E : (String → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (set v : EM σ PUnit) Q E s = Q ⟨⟩ v := rfl
theorem wp_throw_EM {α : Type} (e : String) (Q : α → σ → Prop) (E : (String → σ → Prop) × EStack⟨⟩)
    (s : σ) : wp (throw e : EM σ α) Q E s = E.1 e s := rfl
theorem wp_throwIf_EM (b : Bool) (e : String) (Q : Unit → σ → Prop)
    (E : (String → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (throwIf b e : EM σ Unit) Q E s = if b then E.1 e s else Q () s := by
  cases b <;> rfl

theorem wrp_get_SM {Q : σ → σ → σ → Prop} {E : EStack⟨⟩} :
    (fun s => ∀ x, PureRefinement s x True Eq → Q s x s)
      ⊑ wrp (γ σ) (get : SM σ σ) (get : SM σ σ) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_get_SM] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨s, h.1 s (PureRefinement.of_rel rfl), h.2⟩

theorem wrp_set_SM (v w : σ) {Q : PUnit → PUnit → σ → Prop} {E : EStack⟨⟩} :
    (fun _ => PureRefinement v w True Eq ∧ Q ⟨⟩ ⟨⟩ v)
      ⊑ wrp (γ σ) (set v : SM σ PUnit) (set w : SM σ PUnit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_set_SM] at h ⊢
  obtain ⟨⟨hv, hq⟩, ha⟩ := h
  cases (hv trivial : v = w)
  rw [Concretization.post_pi]
  exact ⟨⟨⟩, hq, ha⟩

theorem wrp_pure_unit_SM {Q : Unit → Unit → σ → Prop} {E : EStack⟨⟩} :
    Q () () ⊑ wrp (γ σ) (pure () : SM σ Unit) (pure () : SM σ Unit) Q E :=
  wrp_pure () ()

theorem wrp_pure_SM {α : Type} (c a : α) {Q : α → α → σ → Prop} {E : EStack⟨⟩} :
    (fun s => PureRefinement c a True Eq ∧ Q c a s)
      ⊑ wrp (γ σ) (pure c : SM σ α) (pure a : SM σ α) Q E :=
  fun s h => wrp_pure (Q := Q) (E := E) c a s h.2

theorem wrp_get_EM {Q : σ → σ → σ → Prop} {E : ER σ} :
    (fun s => ∀ x, PureRefinement s x True Eq → Q s x s)
      ⊑ wrp (γ σ) (get : EM σ σ) (get : EM σ σ) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_get_EM] at h ⊢
  rw [Concretization.post_pi]
  exact ⟨s, h.1 s (PureRefinement.of_rel rfl), h.2⟩

theorem wrp_set_EM (v w : σ) {Q : PUnit → PUnit → σ → Prop} {E : ER σ} :
    (fun _ => PureRefinement v w True Eq ∧ Q ⟨⟩ ⟨⟩ v)
      ⊑ wrp (γ σ) (set v : EM σ PUnit) (set w : EM σ PUnit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_set_EM] at h ⊢
  obtain ⟨⟨hv, hq⟩, ha⟩ := h
  cases (hv trivial : v = w)
  rw [Concretization.post_pi]
  exact ⟨⟨⟩, hq, ha⟩

theorem wrp_throw_EM {α : Type} (e : String) {Q : α → α → σ → Prop} {E : ER σ} :
    (fun s => E.1 e e s) ⊑ wrp (γ σ) (throw e : EM σ α) (throw e : EM σ α) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_throw_EM] at h ⊢
  show (Concretization.id (σ → Prop)).post E.1 Ea.1 e s
  rw [Concretization.post_pi]
  exact ⟨e, h.1, h.2⟩

theorem wrp_throw_bind_EM {α β : Type} (e : String) (k : α → EM σ β) {Q : β → β → σ → Prop}
    {E : ER σ} :
    (fun s => E.1 e e s) ⊑ wrp (γ σ) (throw e >>= k : EM σ β) (throw e : EM σ β) Q E :=
  PartialOrder.rel_trans (wrp_throw_EM e) (wrp_le_wrp_of_eq (γ := γ σ) (a := (throw e : EM σ β))
    (rfl : (throw e >>= k : EM σ β) = throw e) Q E)

theorem wrp_throwIf_EM (c b : Bool) (e : String) {Q : Unit → Unit → σ → Prop} {E : ER σ} :
    (fun s => PureRefinement c b True Eq ∧ (b = true → E.1 e e s) ∧ (b = false → Q () () s))
      ⊑ wrp (γ σ) (throwIf c e : EM σ Unit) (throwIf b e : EM σ Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s h
  simp only [meet_apply, meet_prop_eq_and, Concretization.id, id_eq, wp_throwIf_EM] at h ⊢
  obtain ⟨⟨hc, ht, hf⟩, ha⟩ := h
  cases (hc trivial : c = b)
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte] at ha ⊢
    rw [Concretization.post_pi]
    exact ⟨(), hf rfl, ha⟩
  · simp only [↓reduceIte] at ha ⊢
    show (Concretization.id (σ → Prop)).post E.1 Ea.1 e s
    rw [Concretization.post_pi]
    exact ⟨e, ht rfl, ha⟩

theorem wrp_pure_unit_EM {Q : Unit → Unit → σ → Prop} {E : ER σ} :
    Q () () ⊑ wrp (γ σ) (pure () : EM σ Unit) (pure () : EM σ Unit) Q E :=
  wrp_pure () ()

end

/-! ## Values -/

theorem abs_refl {α : Type} {c : α} : PureRefinement c c True Eq := fun _ => rfl

theorem abs_add {a b x y : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq := fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

theorem abs_sub {a b x y : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a - b) (x - y) (P₁ ∧ P₂) Eq := fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

theorem abs_gt {a b x y : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a > b) (x > y) (P₁ ∧ P₂) Eq := fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

theorem abs_blt {a b x y : Nat} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (Nat.blt a b) (Nat.blt x y) (P₁ ∧ P₂) Eq := fun ⟨p₁, p₂⟩ => by rw [h₁ p₁, h₂ p₂]

end DistillBench.State
