import Std.WP

/-!
# `WPMonadExact`: exact weakest-precondition monads

`WPMonad` makes a monad's `wp` *sound*: it lower-bounds the postcondition on `pure` and the
decomposition on `bind`. `WPMonadExact` adds the matching upper bounds, so `wp` *computes* `pure`
and `bind`. The abstract side of a refinement proof needs this, since its `wp` is decomposed out of
the precondition.

Instances cover the deterministic / demonic monads: the leaves `Id`, `Option`, `Except`, `EStateM`,
and the transformers `StateT`, `ExceptT`, `OptionT`, each transporting exactness from its base.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

/-- The weakest-precondition interpretation is exact: beyond `WPMonad` soundness it also upper-bounds
`pure`/`bind`, so the two together compute them. The abstract side of `wrp` needs this, since its
`wp` is decomposed out of the precondition. A mixin over `WPMonad` rather than an extension, so it
never participates in `WP` synthesis. -/
class WPMonadExact (m : Type u → Type v) (Pred : Type w) (EPred : Type w')
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] : Prop where
  /-- `wp` upper-bounds the postcondition on `pure`. -/
  wp_pure_le {α : Type u} (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost ⊑ post a
  /-- `wp` upper-bounds the `bind` decomposition. -/
  wp_bind_le {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost

/-- Exact `wp` computes `pure`. -/
theorem WPMonadExact.wp_pure_eq {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [WPMonadExact m Pred EPred]
    {α} (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost = post a :=
  PartialOrder.rel_antisymm (WPMonadExact.wp_pure_le a post epost) (WPMonad.pure_le_wp_pure a post epost)

/-- Exact `wp` computes `bind`. -/
theorem WPMonadExact.wp_bind_eq {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [WPMonadExact m Pred EPred]
    {α β} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost :=
  PartialOrder.rel_antisymm (WPMonadExact.wp_bind_le x f post epost)
    (WPMonad.bind_le_wp_bind x f post epost)

/-! ## Leaf instances -/

instance : WPMonadExact Id Prop EPost.Nil where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun _ _ _ _ => PartialOrder.rel_refl

instance : WPMonadExact Option.{u} Prop Prop where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun x _ _ _ => by cases x <;> exact PartialOrder.rel_refl

instance {ε : Type u} : WPMonadExact (Except ε) Prop EPost⟨ε → Prop⟩ where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun x _ _ _ => by cases x <;> exact PartialOrder.rel_refl

instance {ε σ : Type} : WPMonadExact (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wp_pure_le := fun _ _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun x _ _ _ s => by
    simp only [WP.wp, WP.wpTrans, bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl

/-! ## Transformer instances: exactness transports from the base monad -/

instance {σ : Type u} {m : Type u → Type v} {Pred : Type w} {EPred : Type v}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [WPMonadExact m Pred EPred] :
    WPMonadExact (StateT σ m) (σ → Pred) EPred where
  wp_pure_le a := fun post epost s =>
    WPMonadExact.wp_pure_le (m := m) (a, s) (fun p => post p.1 p.2) epost
  wp_bind_le x f := fun _ _ _ => by apply WPMonadExact.wp_bind_le

instance {ε : Type u} {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [WPMonadExact m Pred EPred] :
    WPMonadExact (ExceptT ε m) Pred (EPost.Cons (ε → Pred) EPred) where
  wp_pure_le a := fun post epost =>
    WPMonadExact.wp_pure_le (m := m) (Except.ok a) (epost.pushExcept post) epost.tail
  wp_bind_le x f := fun post epost => by
    show wp (x >>= f).run (epost.pushExcept post) epost.tail ⊑ wp x.run _ epost.tail
    apply PartialOrder.rel_trans
      (WPMonadExact.wp_bind_le (m := m) x.run _ (epost.pushExcept post) epost.tail)
    apply WP.wp_consequence
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error el =>
      exact WPMonadExact.wp_pure_le (m := m) (Except.error el) (epost.pushExcept post) epost.tail

instance {m : Type u → Type v} {Pred : Type u} {EPred : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] [WPMonadExact m Pred EPred] :
    WPMonadExact (OptionT m) Pred (EPost.Cons Pred EPred) where
  wp_pure_le a := fun post epost =>
    WPMonadExact.wp_pure_le (m := m) (some a) (epost.pushOption post) epost.tail
  wp_bind_le x f := fun post epost => by
    show wp (x >>= f).run (epost.pushOption post) epost.tail ⊑ wp x.run _ epost.tail
    apply PartialOrder.rel_trans
      (WPMonadExact.wp_bind_le (m := m) x.run _ (epost.pushOption post) epost.tail)
    apply WP.wp_consequence
    intro r; cases r with
    | some a => exact PartialOrder.rel_refl
    | none =>
      exact WPMonadExact.wp_pure_le (m := m) none (epost.pushOption post) epost.tail

end Ascent
