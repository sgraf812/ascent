import Ascent.Corres.Basic
import AscentTests.WordAbstraction

/-!
# A demonic failure effect for guards

`Dem` is `Option` with a *demonic* weakest precondition: `wp fail = ⊥`, so a failed guard makes
every postcondition unprovable. This is the monad in which AutoCorres' emitted `guard` statements
live. A value-dependent side-condition (e.g. no-overflow) rides along inside the abstract program
and is threaded by `wp` through `bind`, instead of being a precondition on the relation. The
word-overflow `bind` that could not be related unconditionally now goes through: on bad values the
abstract program fails (`wp = ⊥`), discharging the correspondence trivially.
-/

open Std.Internal.Do Lean.Order Ascent

/-- `Option` reinterpreted with a demonic `wp`: failure is `⊥`, not a handled exception. -/
def Dem (α : Type) := Option α

namespace Dem

instance : Monad Dem := inferInstanceAs (Monad Option)
instance : LawfulMonad Dem := inferInstanceAs (LawfulMonad Option)

/-- Demonic failure. -/
def fail : Dem α := none

/-- Return `a`, but fail (demonically) unless the guard `g` holds. -/
def guardRet (g : Prop) [Decidable g] (a : α) : Dem α := if g then pure a else fail

@[instance_reducible] def wpInst {α} : WP (Dem α) α Prop EPost.Nil where
  wpTrans x := ⟨fun post _ => match x with | none => ⊥ | some a => post a⟩
  wp_trans_monotone x := by
    intro post post' epost epost' _ hpost
    cases x with
    | none => exact PartialOrder.rel_refl
    | some a => exact hpost a

instance instWPMonad : WPMonad Dem Prop EPost.Nil where
  toWP _ := wpInst
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f := by intro post epost; cases x <;> exact PartialOrder.rel_refl

@[simp] theorem wp_pure_eq {α} (a : α) (Q : α → Prop) (E : EPost.Nil) :
    wp (pure a : Dem α) Q E = Q a := rfl

@[simp] theorem wp_fail_eq {α} (Q : α → Prop) (E : EPost.Nil) :
    wp (Dem.fail : Dem α) Q E = ⊥ := rfl

theorem wp_pure_le {α} (a : α) (post : α → Prop) (epost : EPost.Nil) :
    wp (pure a : Dem α) post epost ⊑ post a := PartialOrder.rel_refl

theorem wp_bind_le {α β} (x : Dem α) (f : α → Dem β) (post : β → Prop) (epost : EPost.Nil) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost := by
  cases x <;> exact PartialOrder.rel_refl

end Dem

/-- The structural laws for an abstraction into `Dem` (`Dem`'s `wp` is a monad morphism). -/
instance : LawfulRefinement (idRefinement Prop EPost.Nil) Id Dem :=
  .ofWPMorphism Dem.wp_pure_le Dem.wp_bind_le

/-- A guarded pure value abstracts a pure value, when the guard implies the value relation. The
no-overflow obligation lives in the guard `g`, threaded by `wp`, not in a precondition. -/
theorem corres_guardRet {CVal AVal} {g : Prop} [Decidable g] (γV : CVal → AVal)
    {a : AVal} {c : CVal} (h : g → γV c = a) :
    Corres (idRefinement Prop EPost.Nil) γV (Dem.guardRet g a) (pure c : Id CVal) := by
  intro Q E
  by_cases hg : g
  · have hh : γV c = a := h hg
    subst hh
    rw [show Dem.guardRet g (γV c) = pure (γV c) from by simp [Dem.guardRet, hg]]
    exact PartialOrder.rel_refl
  · rw [show Dem.guardRet g a = Dem.fail from by simp [Dem.guardRet, hg]]
    show (⊥ : Prop) ⊑ Q (γV c)
    exact bot_le _

/-- The word-overflow `bind` that was impossible without guards: a second operation whose
overflow depends on the first operation's *result*. The continuation guards on no-overflow, so the
correspondence holds for every intermediate value. -/
example (a b c : UInt64) (h1 : a.toNat + b.toNat < 2 ^ 64) :
    Corres (idRefinement Prop EPost.Nil) wordγV
      (do let r ← pure (wordγV a + wordγV b)
          Dem.guardRet (r * wordγV c < 2 ^ 64) (r * wordγV c) : Dem Int)
      (do let r ← pure (a + b); pure (r * c) : Id UInt64) := by
  refine corres_bind wordγV wordγV ?_ (fun cv => ?_)
  · apply corres_pure
    show wordγV (a + b) = wordγV a + wordγV b
    simp only [wordγV, UInt64.toNat_add, Nat.mod_eq_of_lt h1]
    omega
  · apply corres_guardRet
    intro hovf
    show wordγV (cv * c) = wordγV cv * wordγV c
    have hlt : cv.toNat * c.toNat < 2 ^ 64 := by
      simp only [wordγV] at hovf; omega
    simp only [wordγV, UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]
    rfl
