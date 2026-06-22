import Std.Internal.Do

/-!
# `Corres`: soundness of monadic abstraction

`Corres r γV a c` states that the abstract program `a` soundly abstracts the concrete
program `c`: any property proved of `a` transports to `c`. It is read as abstract
interpretation, `r.γP (wp a Q E) ⊑ wp c (r.γQ γV Q) (r.γE E)`, where the abstract program's
predicate transformer, concretized by `r`, lower-bounds the concrete one.

`Refinement` carries the monad-level concretizations `γP`/`γE` (independent of the value
type). The value abstraction `γV` is a per-`Corres` argument because `bind` relates programs
at different value types.

`corres_bind` needs the reverse direction of the one-directional `WPMonad` soundness axioms on
the abstract side. `LawfulRefinement` packages the structural laws; `LawfulRefinement.ofWPMorphism`
discharges them whenever the abstract `wp` is a monad morphism.
-/

open Std.Internal.Do Lean.Order

namespace Ascent

universe u v w w'

/-- If `wp` lower-bounds the postcondition on `pure` (one direction of being a monad
morphism), then with `WPMonad` it computes `pure` exactly. -/
theorem wp_pure_eq {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (wp_pure_le : ∀ {α} (a : α) (post : α → Pred) (epost : EPred),
      wp (pure a : m α) post epost ⊑ post a)
    {α} (a : α) (post : α → Pred) (epost : EPred) :
    wp (pure a : m α) post epost = post a :=
  PartialOrder.rel_antisymm (wp_pure_le a post epost) (WPMonad.pure_le_wp_pure a post epost)

/-- If `wp` lower-bounds the decomposition on `bind`, then with `WPMonad` it computes `bind`
exactly. -/
theorem wp_bind_eq {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (wp_bind_le : ∀ {α β} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred),
      wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost)
    {α β} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    wp (x >>= f) post epost = wp x (fun a => wp (f a) post epost) epost :=
  PartialOrder.rel_antisymm (wp_bind_le x f post epost) (WPMonad.bind_le_wp_bind x f post epost)

/-- A refinement between two `WP` setups: monad-level concretizations of normal and
exceptional assertions. The value-level abstraction is supplied per `Corres` statement. -/
structure Refinement (CPred : Type w) (APred : Type w) (CEPred : Type w') (AEPred : Type w')
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred] where
  /-- Concretization of normal assertions. -/
  γP : APred → CPred
  /-- Concretization of exceptional assertions. -/
  γE : AEPred → CEPred
  /-- `γP` is monotone. -/
  γP_mono : ∀ {p q : APred}, p ⊑ q → γP p ⊑ γP q
  /-- `γE` is monotone. -/
  γE_mono : ∀ {p q : AEPred}, p ⊑ q → γE p ⊑ γE q

namespace Refinement

variable {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]

/-- Postcondition concretization: pull an abstract postcondition back along the value
abstraction `γV`, then concretize the assertion. -/
def γQ (r : Refinement CPred APred CEPred AEPred) {CVal AVal : Type _}
    (γV : CVal → AVal) (Q : AVal → APred) : CVal → CPred :=
  fun cv => r.γP (Q (γV cv))

end Refinement

/-- The abstract program `a` soundly abstracts the concrete program `c` under refinement `r`
and value abstraction `γV`. -/
def Corres {CProg AProg : Type _} {CVal AVal : Type _}
    {CPred APred : Type w} {CEPred AEPred : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]
    (r : Refinement CPred APred CEPred AEPred) (γV : CVal → AVal) (a : AProg) (c : CProg) :
    Prop :=
  ∀ Q E, r.γP (wp a Q E) ⊑ wp c (r.γQ γV Q) (r.γE E)

/-! ## Structural laws

`corres_pure` and `corres_bind` are the only laws the structural development needs beyond
`Refinement`'s monotonicity. They are the *weakest* requirement, so they form a class keyed on
the refinement rather than a property of the abstract monad: a separation-logic or otherwise
non-morphism abstract interpretation can satisfy them by reasoning that couples both sides
through `γ`. `LawfulRefinement.ofWPMorphism` discharges them when the abstract `wp` is a monad
morphism, the common case. -/

section Structural

variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred]

/-- A refinement whose `pure` and `bind` transport correspondence between `CM` and `AM`. -/
class LawfulRefinement (r : Refinement CPred APred CEPred AEPred)
    (CM AM : Type w → Type v) [Monad CM] [Monad AM]
    [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] : Prop where
  /-- `pure` abstracts `pure` when the returned values correspond. -/
  corres_pure {CVal AVal : Type w} (γV : CVal → AVal) {a : AVal} {c : CVal} (h : γV c = a) :
    Corres r γV (pure a : AM AVal) (pure c : CM CVal)
  /-- `bind` abstracts `bind`: the first computations correspond, and the continuations
  correspond at every concrete intermediate value. -/
  corres_bind {CV AV CV₂ AV₂ : Type w} (γV : CV → AV) (γV₂ : CV₂ → AV₂)
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    (hc : Corres r γV a₁ c₁) (hf : ∀ cv, Corres r γV₂ (a₂ (γV cv)) (c₂ cv)) :
    Corres r γV₂ (a₁ >>= a₂) (c₁ >>= c₂)

export LawfulRefinement (corres_pure corres_bind)

/-- Build the structural laws when the abstract `wp` is a monad morphism: supply the two facts
that `wp` lower-bounds `pure` and `bind`. This is the common case for a concrete abstract
monad; non-morphism abstractions provide a `LawfulRefinement` directly. -/
theorem LawfulRefinement.ofWPMorphism {r : Refinement CPred APred CEPred AEPred}
    (wp_pure_le : ∀ {α : Type w} (a : α) (post : α → APred) (epost : AEPred),
      wp (pure a : AM α) post epost ⊑ post a)
    (wp_bind_le : ∀ {α β : Type w} (x : AM α) (f : α → AM β) (post : β → APred) (epost : AEPred),
      wp (x >>= f) post epost ⊑ wp x (fun a => wp (f a) post epost) epost) :
    LawfulRefinement r CM AM where
  corres_pure := by
    intro CVal AVal γV a c h Q E
    refine PartialOrder.rel_trans (r.γP_mono (wp_pure_le a Q E)) ?_
    have hQ : r.γQ γV Q c = r.γP (Q a) := by simp [Refinement.γQ, h]
    rw [← hQ]
    exact WPMonad.pure_le_wp_pure c (r.γQ γV Q) (r.γE E)
  corres_bind := by
    intro CV AV CV₂ AV₂ γV γV₂ a₁ c₁ a₂ c₂ hc hf Q E
    refine PartialOrder.rel_trans (r.γP_mono (wp_bind_le a₁ a₂ Q E)) ?_
    refine PartialOrder.rel_trans (hc (fun av => wp (a₂ av) Q E) E) ?_
    refine PartialOrder.rel_trans
      (WP.wp_consequence c₁ (r.γQ γV (fun av => wp (a₂ av) Q E))
        (fun cv => wp (c₂ cv) (r.γQ γV₂ Q) (r.γE E)) (r.γE E) (fun cv => hf cv Q E)) ?_
    exact WPMonad.bind_le_wp_bind c₁ c₂ (r.γQ γV₂ Q) (r.γE E)

/-- Branch congruence on a shared condition. -/
theorem corres_ite (r : Refinement CPred APred CEPred AEPred) {CVal AVal : Type w}
    (γV : CVal → AVal) {cond : Prop} [Decidable cond] {a₁ a₂ : AM AVal} {c₁ c₂ : CM CVal}
    (h₁ : Corres r γV a₁ c₁) (h₂ : Corres r γV a₂ c₂) :
    Corres r γV (if cond then a₁ else a₂) (if cond then c₁ else c₂) := by
  by_cases hc : cond <;> simp only [hc, if_true, if_false] <;> assumption

end Structural

/-! ## Composition of refinements -/

section Comp

variable {CPred BPred APred : Type w} {CEPred BEPred AEPred : Type w'}
  [Assertion CPred] [Assertion BPred] [Assertion APred]
  [Assertion CEPred] [Assertion BEPred] [Assertion AEPred]

/-- Compose refinements `C ← B` and `B ← A` into `C ← A`. -/
def Refinement.comp (r₁ : Refinement CPred BPred CEPred BEPred)
    (r₂ : Refinement BPred APred BEPred AEPred) : Refinement CPred APred CEPred AEPred where
  γP := r₁.γP ∘ r₂.γP
  γE := r₁.γE ∘ r₂.γE
  γP_mono h := r₁.γP_mono (r₂.γP_mono h)
  γE_mono h := r₁.γE_mono (r₂.γE_mono h)

/-- Correspondence composes: composing the refinements and the value abstractions. -/
theorem corres_comp {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
    [WP CProg CVal CPred CEPred] [WP BProg BVal BPred BEPred] [WP AProg AVal APred AEPred]
    {r₁ : Refinement CPred BPred CEPred BEPred} {r₂ : Refinement BPred APred BEPred AEPred}
    {γV₁ : CVal → BVal} {γV₂ : BVal → AVal} {a : AProg} {b : BProg} {c : CProg}
    (hc : Corres r₁ γV₁ b c) (hb : Corres r₂ γV₂ a b) :
    Corres (r₁.comp r₂) (γV₂ ∘ γV₁) a c := by
  intro Q E
  exact PartialOrder.rel_trans (r₁.γP_mono (hb Q E)) (hc (r₂.γQ γV₂ Q) (r₂.γE E))

/-- Correspondence is transitive across composed refinements, so it chains in `calc`. With
`corres_id` as the identity, `Corres` forms a category (programs as objects, refinements as
arrows); the homogeneous identity-refinement slice is a preorder. -/
instance {CProg BProg AProg : Type _} {CVal BVal AVal : Type _}
    [WP CProg CVal CPred CEPred] [WP BProg BVal BPred BEPred] [WP AProg AVal APred AEPred]
    {r₁ : Refinement CPred BPred CEPred BEPred} {r₂ : Refinement BPred APred BEPred AEPred}
    {γV₁ : CVal → BVal} {γV₂ : BVal → AVal} :
    Trans (Corres r₂ γV₂ : AProg → BProg → Prop) (Corres r₁ γV₁ : BProg → CProg → Prop)
      (Corres (r₁.comp r₂) (γV₂ ∘ γV₁) : AProg → CProg → Prop) where
  trans hab hbc := corres_comp hbc hab

end Comp

/-! ## Identity refinement

The refinement that leaves assertions unchanged. Value abstraction is still supplied per
`Corres`, so this is the refinement for phases that abstract only values (word abstraction). -/

section Id

variable {Pred : Type w} {EPred : Type w'} [Assertion Pred] [Assertion EPred]

/-- The refinement that is the identity on both assertion lattices. -/
def idRefinement (Pred : Type w) (EPred : Type w') [Assertion Pred] [Assertion EPred] :
    Refinement Pred Pred EPred EPred where
  γP := id
  γE := id
  γP_mono h := h
  γE_mono h := h

/-- Every program abstracts itself under the identity refinement: the identity of the
correspondence category. -/
theorem corres_id {Prog Val : Type _} [WP Prog Val Pred EPred] (x : Prog) :
    Corres (idRefinement Pred EPred) (id : Val → Val) x x :=
  fun _ _ => PartialOrder.rel_refl

end Id

end Ascent
