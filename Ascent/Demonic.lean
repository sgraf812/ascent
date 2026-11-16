import Ascent.Refinement

/-!
# The `Demonic` effect

A program in `Demonic α` is a positively conjunctive predicate transformer: `x.wpD Q` holds if
every run of `x` ends in a value that satisfies `Q`, and `x.wpD` preserves every nonempty
conjunction of postconditions. Every such transformer is `abort` (undefined behaviour,
`wp = ⊥`) or `select p` (any value satisfying `p`, `wp Q = ∀ a, p a → Q a`): a singleton `p` is
determined behaviour, a larger `p` unspecified behaviour, and `p = ∅` is `magic`, a program
without outcome. A `bind` aborts if its first program aborts or if the continuation aborts at one
of its values.

`assert g` continues if `g` holds and aborts otherwise. `assume g` continues if `g` holds and is
`magic` otherwise. `havoc` returns any value. An abstract program carries the side conditions of
the concrete program, such as mapped memory, as `assert`s, and it states the values that the
concrete program leaves unspecified with `havoc` or `select`.

Programs are equal if their `wp`s are (`Demonic.ext`). The outcome sets of `Demonic.Internal` are a
proof device of this library.
-/

open Std.WP Lean.Order Ascent

/-- `t` maps every nonempty conjunction of postconditions to the conjunction of its images. -/
def Conj {α : Type} (t : (α → Prop) → Prop) : Prop :=
  ∀ (ι : Type) [Nonempty ι] (Q : ι → α → Prop), t (fun a => ∀ i, Q i a) ↔ ∀ i, t (Q i)

@[ext] structure Demonic (α : Type) where private mk ::
  wpD : (α → Prop) → Prop
  conj : Conj wpD

namespace Demonic

theorem mono {α : Type} (x : Demonic α) {Q Q' : α → Prop} (h : ∀ a, Q a → Q' a) (hx : x.wpD Q) :
    x.wpD Q' := by
  have hQ : Q = fun a => ∀ i : Bool, (if i then Q' else Q) a :=
    funext fun a => propext ⟨fun hq i => by cases i <;> simp [hq, h a hq], fun hq => hq false⟩
  rw [hQ, x.conj] at hx
  exact hx true

/-- Undefined behaviour. -/
def abort {α : Type} : Demonic α :=
  ⟨fun _ => False, fun _ _ _ => ⟨False.elim, fun h => h (Classical.ofNonempty)⟩⟩

/-- Any value that satisfies `p`. -/
def select {α : Type} (p : α → Prop) : Demonic α :=
  ⟨fun Q => ∀ a, p a → Q a,
    fun _ _ _ => ⟨fun h i a hs => h a hs i, fun h a hs i => h i a hs⟩⟩

/-- No outcome. -/
def magic {α : Type} : Demonic α := select fun _ => False

@[simp] theorem wpD_abort {α : Type} (Q : α → Prop) : (abort : Demonic α).wpD Q = False := rfl

@[simp] theorem wpD_select {α : Type} (p : α → Prop) (Q : α → Prop) :
    (select p).wpD Q = ∀ a, p a → Q a := rfl

@[simp] theorem wpD_magic {α : Type} (Q : α → Prop) : (magic : Demonic α).wpD Q = True :=
  propext ⟨fun _ => trivial, fun _ _ h => h.elim⟩

namespace Internal

/-- The values that `x` may return. -/
def outs {α : Type} (x : Demonic α) (a : α) : Prop := ∀ Q, x.wpD Q → Q a

theorem wpD_iff {α : Type} {x : Demonic α} (ht : x.wpD fun _ => True) (Q : α → Prop) :
    x.wpD Q ↔ ∀ a, outs x a → Q a := by
  refine ⟨fun h a ho => ho Q h, fun h => ?_⟩
  haveI : Nonempty {Q : α → Prop // x.wpD Q} := ⟨⟨_, ht⟩⟩
  have hall := (x.conj {Q : α → Prop // x.wpD Q} fun i => i.1).mpr fun i => i.2
  exact x.mono (fun a ha => h a fun Q hQ => ha ⟨Q, hQ⟩) hall

theorem eq_abort {α : Type} {x : Demonic α} (ht : ¬x.wpD fun _ => True) : x = abort :=
  Demonic.ext (funext fun _ => propext ⟨fun h => ht (x.mono (fun _ _ => trivial) h), False.elim⟩)

theorem cases {α : Type} (x : Demonic α) : x = abort ∨ x = select (outs x) := by
  by_cases ht : x.wpD fun _ => True
  · exact Or.inr (Demonic.ext (funext fun Q => propext (wpD_iff ht Q)))
  · exact Or.inl (eq_abort ht)

end Internal

instance : Monad Demonic where
  pure a := ⟨fun Q => Q a, fun _ _ _ => Iff.rfl⟩
  bind x f := ⟨fun Q => x.wpD fun a => (f a).wpD Q, fun ι _ Q => by
    have h : (fun a => (f a).wpD fun b => ∀ i, Q i b) = fun a => ∀ i, (f a).wpD (Q i) :=
      funext fun a => propext ((f a).conj ι Q)
    show (x.wpD fun a => (f a).wpD fun b => ∀ i, Q i b) ↔ ∀ i, x.wpD fun a => (f a).wpD (Q i)
    rw [h]
    exact x.conj ι fun i a => (f a).wpD (Q i)⟩

@[simp] theorem wpD_pure {α : Type} (a : α) (Q : α → Prop) : (pure a : Demonic α).wpD Q = Q a := rfl

@[simp] theorem wpD_bind {α β : Type} (x : Demonic α) (f : α → Demonic β) (Q : β → Prop) :
    (x >>= f).wpD Q = x.wpD fun a => (f a).wpD Q := rfl

instance : LawfulMonad Demonic := LawfulMonad.mk'
  (id_map := fun _ => rfl) (pure_bind := fun _ _ => rfl) (bind_assoc := fun _ _ _ => rfl)

theorem Internal.outs_pure {α : Type} (a : α) : outs (pure a : Demonic α) a := fun _ h => h

theorem Internal.outs_bind_of {α β : Type} {x : Demonic α} {f : α → Demonic β} {a : α} {b : β}
    (ha : outs x a) (hb : outs (f a) b) : outs (x >>= f) b :=
  fun Q h => hb Q (ha _ h)

/-- Undefined behaviour. -/
def fail {α : Type} : Demonic α := abort

@[simp] theorem wpD_fail {α : Type} (Q : α → Prop) : (fail : Demonic α).wpD Q = False := rfl

/-- Any value. -/
def havoc {α : Type} : Demonic α := select fun _ => True

/-- Continues if `g` holds. Aborts otherwise. -/
def assert (g : Prop) : Demonic Unit :=
  ⟨fun Q => g ∧ Q (), fun _ _ _ =>
    ⟨fun ⟨hg, h⟩ i => ⟨hg, h i⟩, fun h => ⟨(h Classical.ofNonempty).1, fun i => (h i).2⟩⟩⟩

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
  trans x := ⟨fun post _ => x.wpD post⟩
  trans_monotone x := by
    intro post post' epost epost' _ hpost
    exact x.mono hpost

instance instWPMonad : WPMonad Demonic Prop EStack⟨⟩ where
  toWP _ := wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ := by
    intro _ _
    exact PartialOrder.rel_refl

theorem wp_eq {α : Type} (x : Demonic α) (Q : α → Prop) (E : EStack⟨⟩) : wp x Q E = x.wpD Q := rfl

@[simp] theorem wp_pure_eq {α : Type} (a : α) (Q : α → Prop) (E : EStack⟨⟩) :
    wp (pure a : Demonic α) Q E = Q a := rfl

@[simp] theorem wp_havoc_eq {α : Type} (Q : α → Prop) (E : EStack⟨⟩) :
    wp (havoc : Demonic α) Q E = ∀ a, Q a :=
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
    (hP : wp x P epost) (hR : wp x R epost) : wp x (fun a => P a ∧ R a) epost := by
  have := (x.conj Bool fun i => if i then P else R).mpr fun i => by cases i <;> assumption
  exact x.mono (fun a h => ⟨by simpa using h true, by simpa using h false⟩) this

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

theorem Ascent.Refinement.assert_pure {AV CV : Type} {g : Prop} {P : Prop}
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
