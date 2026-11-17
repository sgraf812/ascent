import Distillery.Refinement

/-!
# The `Demonic` effect

A program in `Demonic α` is a finitely conjunctive predicate transformer: `x.wpD Q` holds if
every run of `x` ends in a value that satisfies `Q`, `x.wpD` is monotone, and it preserves binary
conjunctions of postconditions. Every such transformer is `abort` (undefined behaviour,
`wp = ⊥`) or the filter `{Q | x.wpD Q}` on `α` (`selectFilter`). The principal filter of `p` is
`select p` (any value satisfying `p`, `wp Q = ∀ a, p a → Q a`): a singleton `p` is determined
behaviour, a larger `p` unspecified behaviour, and `p = ∅` is `magic`, a program without outcome.
A `bind` aborts if its first program aborts or if the continuation aborts on a set of values
whose complement is outside the filter of the first program.

`assert g` continues if `g` holds and aborts otherwise. `assume g` continues if `g` holds and is
`magic` otherwise. `unknown` returns any value. An abstract program carries the side conditions of
the concrete program, such as mapped memory, as `assert`s, and it states the values that the
concrete program leaves unspecified with `unknown` or `select`.

Programs are equal if their `wp`s are (`Demonic.ext`). A Mathlib `Filter` gives a program through
`selectFilter`. The values in every set of the filter (`Demonic.Internal.outs`) can be empty, as for
the filter of large enough numbers, so proofs about runs use `wpD` and `meet`, not outcome sets.
-/

open Std.WP Lean.Order Distillery

@[ext] structure Demonic (α : Type) where private mk ::
  wpD : (α → Prop) → Prop
  mono : ∀ {Q Q' : α → Prop}, (∀ a, Q a → Q' a) → wpD Q → wpD Q'
  meet : ∀ {Q Q' : α → Prop}, wpD Q → wpD Q' → wpD fun a => Q a ∧ Q' a

namespace Demonic

/-- Undefined behaviour. -/
def abort {α : Type} : Demonic α := ⟨fun _ => False, fun _ h => h, fun h _ => h⟩

/-- Any value that satisfies `p`. -/
def select {α : Type} (p : α → Prop) : Demonic α :=
  ⟨fun Q => ∀ a, p a → Q a, fun h hx a hp => h a (hx a hp),
    fun h₁ h₂ a hp => ⟨h₁ a hp, h₂ a hp⟩⟩

/-- Any value in a set of the filter `F`. -/
def selectFilter {α : Type} (F : (α → Prop) → Prop)
    (mono : ∀ {Q Q' : α → Prop}, (∀ a, Q a → Q' a) → F Q → F Q')
    (meet : ∀ {Q Q' : α → Prop}, F Q → F Q' → F fun a => Q a ∧ Q' a) : Demonic α :=
  ⟨F, mono, meet⟩

/-- No outcome. -/
def magic {α : Type} : Demonic α := select fun _ => False

@[simp] theorem wpD_abort {α : Type} (Q : α → Prop) : (abort : Demonic α).wpD Q = False := rfl

@[simp] theorem wpD_select {α : Type} (p : α → Prop) (Q : α → Prop) :
    (select p).wpD Q = ∀ a, p a → Q a := rfl

@[simp] theorem wpD_selectFilter {α : Type} (F : (α → Prop) → Prop) (h₁ h₂) (Q : α → Prop) :
    (selectFilter F h₁ h₂).wpD Q = F Q := rfl

@[simp] theorem wpD_magic {α : Type} (Q : α → Prop) : (magic : Demonic α).wpD Q = True :=
  propext ⟨fun _ => trivial, fun _ _ h => h.elim⟩

namespace Internal

/-- The values that every set of the filter of `x` contains. -/
def outs {α : Type} (x : Demonic α) (a : α) : Prop := ∀ Q, x.wpD Q → Q a

end Internal

instance : Monad Demonic where
  pure a := ⟨fun Q => Q a, fun h hq => h _ hq, fun h₁ h₂ => ⟨h₁, h₂⟩⟩
  bind x f := ⟨fun Q => x.wpD fun a => (f a).wpD Q, fun h => x.mono fun a => (f a).mono h,
    fun h₁ h₂ => x.mono (fun a h => (f a).meet h.1 h.2) (x.meet h₁ h₂)⟩

@[simp] theorem wpD_pure {α : Type} (a : α) (Q : α → Prop) : (pure a : Demonic α).wpD Q = Q a := rfl

@[simp] theorem wpD_bind {α β : Type} (x : Demonic α) (f : α → Demonic β) (Q : β → Prop) :
    (x >>= f).wpD Q = x.wpD fun a => (f a).wpD Q := rfl

instance : LawfulMonad Demonic := LawfulMonad.mk'
  (id_map := fun _ => rfl) (pure_bind := fun _ _ => rfl) (bind_assoc := fun _ _ _ => rfl)

/-- Undefined behaviour. -/
def fail {α : Type} : Demonic α := abort

@[simp] theorem wpD_fail {α : Type} (Q : α → Prop) : (fail : Demonic α).wpD Q = False := rfl

/-- Any value. -/
def unknown {α : Type} : Demonic α := select fun _ => True

/-- Continues if `g` holds. Aborts otherwise. -/
def assert (g : Prop) : Demonic Unit :=
  ⟨fun Q => g ∧ Q (), fun h hq => ⟨hq.1, h _ hq.2⟩, fun h₁ h₂ => ⟨h₁.1, h₁.2, h₂.2⟩⟩

theorem assert_of_pos {g : Prop} (h : g) : assert g = pure () :=
  Demonic.ext (funext fun _ => propext ⟨And.right, fun hq => ⟨h, hq⟩⟩)

theorem assert_of_neg {g : Prop} (h : ¬g) : assert g = fail :=
  Demonic.ext (funext fun _ => propext ⟨fun hq => h hq.1, False.elim⟩)

@[simp] theorem assert_true : assert True = pure () := assert_of_pos trivial

/-- Continues if `g` holds. Has no outcome otherwise. -/
def assume (g : Prop) : Demonic Unit := select fun _ => g

theorem assume_of_pos {g : Prop} (h : g) : assume g = pure () :=
  Demonic.ext (funext fun _ => propext ⟨fun hq => hq () h, fun hq _ _ => hq⟩)

theorem assume_of_neg {g : Prop} (h : ¬g) : assume g = magic :=
  Demonic.ext (funext fun _ => propext ⟨fun _ _ hf => hf.elim, fun _ _ hg => (h hg).elim⟩)

theorem fail_bind {α β : Type} (f : α → Demonic β) : (fail >>= f) = fail := rfl

theorem assert_bind_of_pos {α : Type} {g : Prop} (h : g) (f : Unit → Demonic α) :
    (assert g >>= f) = f () := by
  rw [assert_of_pos h, pure_bind]

theorem assert_bind_of_neg {α : Type} {g : Prop} (h : ¬g) (f : Unit → Demonic α) :
    (assert g >>= f) = fail := by
  rw [assert_of_neg h]
  rfl

@[instance_reducible] def wpInst {α : Type} : WP (Demonic α) α Prop EStack⟨⟩ where
  trans x := PredTrans.mk (fun post _ => x.wpD post) fun hpost _ => x.mono hpost

instance instWPMonad : WPMonad Demonic Prop EStack⟨⟩ where
  toWP _ := wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ := by
    intro _ _
    exact PartialOrder.rel_refl

theorem wp_eq {α : Type} (x : Demonic α) (Q : α → Prop) (E : EStack⟨⟩) : wp x Q E = x.wpD Q := rfl

@[simp] theorem wp_pure_eq {α : Type} (a : α) (Q : α → Prop) (E : EStack⟨⟩) :
    wp (pure a : Demonic α) Q E = Q a := rfl

@[simp] theorem wp_unknown_eq {α : Type} (Q : α → Prop) (E : EStack⟨⟩) :
    wp (unknown : Demonic α) Q E = ∀ a, Q a :=
  propext ⟨fun h a => h a trivial, fun h a _ => h a⟩

@[simp] theorem wp_fail_eq {α : Type} (Q : α → Prop) (E : EStack⟨⟩) :
    wp (Demonic.fail : Demonic α) Q E = ⊥ := by
  rw [bot_prop_eq]
  rfl

theorem wp_bind_eq {α β : Type} (x : Demonic α) (f : α → Demonic β) (post : β → Prop) (epost : EStack⟨⟩) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost := rfl

@[simp] theorem wp_map_eq {α β : Type} (f : α → β) (x : Demonic α) (Q : β → Prop) (E : EStack⟨⟩) :
    wp (f <$> x) Q E = wp x (fun a => Q (f a)) E := by
  rw [map_eq_pure_bind, wp_bind_eq]
  simp only [wp_pure_eq]

theorem wp_assert_eq (g : Prop) (Q : Unit → Prop) (E : EStack⟨⟩) :
    wp (assert g) Q E = (g ∧ Q ()) := rfl

theorem wp_assume_eq (g : Prop) (Q : Unit → Prop) (E : EStack⟨⟩) :
    wp (assume g) Q E = (g → Q ()) :=
  propext ⟨fun h hg => h () hg, fun h _ hg => h hg⟩

@[simp] theorem wp_magic_eq {α : Type} (Q : α → Prop) (E : EStack⟨⟩) :
    wp (magic : Demonic α) Q E = True := wpD_magic Q

@[simp] theorem wp_select_eq {α : Type} (p : α → Prop) (Q : α → Prop) (E : EStack⟨⟩) :
    wp (select p) Q E = ∀ a, p a → Q a := rfl

@[spec] theorem Demonic.fail_spec :
    ⦃⊥⦄ Demonic.fail ⦃Q; E⦄ := ⟨bot_le _⟩

theorem wp_pure_le {α : Type} (a : α) (post : α → Prop) (epost : EStack⟨⟩) :
    wp (pure a : Demonic α) post epost ⊑ post a := PartialOrder.rel_refl

theorem wp_bind_le {α β : Type} (x : Demonic α) (f : α → Demonic β) (post : β → Prop) (epost : EStack⟨⟩) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost := PartialOrder.rel_refl

theorem wp_and {α : Type} (x : Demonic α) (P R : α → Prop) (epost : EStack⟨⟩)
    (hP : wp x P epost) (hR : wp x R epost) : wp x (fun a => P a ∧ R a) epost := x.meet hP hR

theorem wp_meet {α : Type} (x : Demonic α) (A B : α → Prop) (E : EStack⟨⟩) :
    wp x A E ⊓ wp x B E ⊑ wp x (fun v => A v ⊓ B v) E := by
  intro h
  rw [meet_prop_eq_and] at h
  have := wp_and x A B E h.1 h.2
  exact x.mono (fun a ha => by rw [meet_prop_eq_and]; exact ha) this

end Demonic

@[simp] theorem top_meet {α} [Assertion α] (x : α) : (⊤ : α) ⊓ x = x :=
  PartialOrder.rel_antisymm (meet_le_right _ _) (le_meet _ _ _ (le_top _) PartialOrder.rel_refl)

@[simp] theorem wp_ite {Prog Value Pred EPosts} [Assertion Pred] [Assertion EPosts]
    [WP Prog Value Pred EPosts] (c : Prop) [Decidable c]
    (a b : Prog) (post : Value → Pred) (epost : EPosts) :
    wp (if c then a else b) post epost = if c then wp a post epost else wp b post epost := by
  split <;> rfl

instance : WPMonadExact Demonic Prop EStack⟨⟩ where
  wp_pure_le := Demonic.wp_pure_le
  wp_bind_le := Demonic.wp_bind_le

instance {α : Type} (x : Demonic α) : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by
    rw [show (Q₁ ⊓ Q₂) = fun v => Q₁ v ⊓ Q₂ v from funext fun v => meet_apply Q₁ Q₂ v]
    exact Demonic.wp_meet x Q₁ Q₂ E₁

theorem Distillery.Refinement.assert_pure {AV CV : Type} {g : Prop} {P : Prop}
    {Q : CV → AV → Prop} (c : CV) (a : AV) (h : g → P ⊑ Q c a) :
    ⦃P⦄ (Pure.pure c : Id CV) ⪯[Concretization.id Prop] (Demonic.assert g >>= fun _ => Pure.pure a) ⦃Q⦄ := by
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  by_cases hg : g
  · rw [Demonic.assert_bind_of_pos hg, Demonic.wp_pure_eq]
    show P ⊓ Qa a ⊑ (Concretization.id Prop).post Q Qa c
    refine le_iSup_of_le a ?_
    exact le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (h hg)) (meet_le_right _ _)
  · rw [Demonic.assert_bind_of_neg hg, Demonic.wp_fail_eq]
    show P ⊓ (⊥ : Prop) ⊑ _
    exact PartialOrder.rel_trans (meet_le_right _ _) (bot_le _)

/-! Monad lifts print as the lifted computation, the way the `do` elaborator inserts them. -/

@[app_unexpander liftM] def unexpandLiftM : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($x)
  | _ => throw ()

@[app_unexpander MonadLiftT.monadLift] def unexpandMonadLift : Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `($x)
  | _ => throw ()
