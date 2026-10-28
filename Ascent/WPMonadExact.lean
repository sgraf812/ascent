import Std.WP

/-!
# Exact weakest preconditions

`WPMonad` states that `wp` is sound for `pure` and `bind`:
`post a ⊑ wp (pure a) post eposts` and
`wp x (fun a => wp (f a) post eposts) eposts ⊑ wp (x >>= f) post eposts`.
`WPMonadExact` adds the converse inequalities. Together they compute `wp` on `pure` and `bind`
(`wp_pure_eq`, `wp_bind_eq`).

The abstract program of a refinement needs this. Its `wp` is a hypothesis in `wrp`, so the
laws of `pure` and `bind` are used in the converse direction. Instances exist for `Id`,
`Option`, `Except`, `EStateM`, `StateT`, `ExceptT` and `OptionT`.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

/-- The converse of the `WPMonad` laws. With them, `wp` computes `pure` and `bind`. -/
class WPMonadExact (m : Type u → Type v) (Pred : Type w) (EPosts : Type w')
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] : Prop where
  /-- `wp (pure a)` is below the postcondition at `a`. -/
  wp_pure_le {α : Type u} (a : α) (post : α → Pred) (epost : EPosts) :
    wp (pure a : m α) post epost ⊑ post a
  /-- `wp (x >>= f)` is below the composition of the two `wp`s. -/
  wp_bind_le {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPosts) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost

theorem WPMonadExact.wp_pure_eq {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m Pred EPosts]
    {α} (a : α) (post : α → Pred) (epost : EPosts) :
    wp (pure a : m α) post epost = post a :=
  PartialOrder.rel_antisymm (WPMonadExact.wp_pure_le a post epost) (WPMonad.pure_le_wp_pure a post epost)

theorem WPMonadExact.wp_bind_eq {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m Pred EPosts]
    {α β} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPosts) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost :=
  PartialOrder.rel_antisymm (WPMonadExact.wp_bind_le x f post epost)
    (WPMonad.bind_le_wp_bind x f post epost)

instance : WPMonadExact Id Prop EStack⟨⟩ where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun _ _ _ _ => PartialOrder.rel_refl

instance : WPMonadExact Option.{u} Prop (Unit → Prop) where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun x _ _ _ => by cases x <;> exact PartialOrder.rel_refl

instance {ε : Type u} : WPMonadExact (Except ε) Prop (ε → Prop) where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun x _ _ _ => by cases x <;> exact PartialOrder.rel_refl

instance {ε σ : Type} : WPMonadExact (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wp_pure_le := fun _ _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun x _ _ _ s => by
    simp only [WP.wp, WP.trans, bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl

instance {σ : Type u} {m : Type u → Type v} {Pred : Type w} {EPosts : Type v}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m Pred EPosts] :
    WPMonadExact (StateT σ m) (σ → Pred) EPosts where
  wp_pure_le a := fun post epost s =>
    WPMonadExact.wp_pure_le (m := m) (a, s) (fun p => post p.1 p.2) epost
  wp_bind_le x f := fun _ _ _ => by apply WPMonadExact.wp_bind_le

instance {ε : Type u} {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m Pred EPosts] :
    WPMonadExact (ExceptT ε m) Pred ((ε → Pred) × EPosts) where
  wp_pure_le a := fun post epost =>
    WPMonadExact.wp_pure_le (m := m) (Except.ok a) (pushExcept post epost.fst) epost.snd
  wp_bind_le x f := fun post epost => by
    show wp (x >>= f).run (pushExcept post epost.fst) epost.snd ⊑ wp x.run _ epost.snd
    apply PartialOrder.rel_trans
      (WPMonadExact.wp_bind_le (m := m) x.run _ (pushExcept post epost.fst) epost.snd)
    apply WP.wp_monotone_post
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error el =>
      exact WPMonadExact.wp_pure_le (m := m) (Except.error el) (pushExcept post epost.fst) epost.snd

instance {m : Type u → Type v} {Pred : Type u} {EPosts : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] [WPMonadExact m Pred EPosts] :
    WPMonadExact (OptionT m) Pred ((Unit → Pred) × EPosts) where
  wp_pure_le a := fun post epost =>
    WPMonadExact.wp_pure_le (m := m) (some a) (pushOption post epost.fst) epost.snd
  wp_bind_le x f := fun post epost => by
    show wp (x >>= f).run (pushOption post epost.fst) epost.snd ⊑ wp x.run _ epost.snd
    apply PartialOrder.rel_trans
      (WPMonadExact.wp_bind_le (m := m) x.run _ (pushOption post epost.fst) epost.snd)
    apply WP.wp_monotone_post
    intro r; cases r with
    | some a => exact PartialOrder.rel_refl
    | none =>
      exact WPMonadExact.wp_pure_le (m := m) none (pushOption post epost.fst) epost.snd

end Ascent
