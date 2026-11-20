import Distillery.Concretization

/-!
# Concretization of exception postconditions

The return relation `Q : CVal → AVal → CPred` relates the values that a concrete and an abstract
program return. The exception relation `E : ERels` relates the values that they throw. `ERels`
mirrors the concrete exception stack, one component per concrete layer:

| `CEPosts` | `AEPosts` | `ERels` |
|---|---|---|
| `EStack⟨⟩` | `EStack⟨⟩` | `EStack⟨⟩` |
| `εc → CPred` | `εa → APred` | `εc → εa → CPred` |
| `εc → CPred` | `EStack⟨⟩` | `εc → CPred` |
| `(εc → CPred) × C` | `(εa → APred) × A` | `(εc → εa → CPred) × ERels'` |
| `(εc → CPred) × C` | `A` | `(εc → CPred) × ERels'` |

A layer that both programs have carries a relation `R`, and `R ec ea` states that the concrete
thrown value `ec` corresponds to the abstract thrown value `ea`. A layer that only the concrete
program has carries a postcondition on the concrete thrown values. Layers align from the
outside in.

`EPostsConcretization.ePosts γ E Ea` is the concrete exception postcondition for the abstract
one `Ea`. On an aligned layer it is `γ.post R Ea`, as `γ.post Q Qa` is on returned values.

An `ExceptT` below a `ReaderT` or a `StateT` has the predicates of its own depth. In
`ExceptT String (ReaderT String (ExceptT Nat (StateT Nat Demonic)))`, the outer layer is
`String → (String → Nat → Prop)` and the inner one `Nat → (Nat → Prop)`. The layers of a product
stack therefore take any predicate types `P` and `P'`, and an aligned layer concretizes by
`LayerConcretization.layer γ : Concretization P P'`: `γ` itself at the depth of `γ`, and the
identity on a predicate type that both programs share.
-/

open Std.WP Lean.Order

namespace Distillery

universe u v₁ v₂ v₃ w w₁ w₂

/-- Computes the type `ERels` of exception relations between the exception stacks `CEPosts`
and `AEPosts`, and the concrete exception postconditions for an exception relation. -/
class EPostsConcretization (CPred APred : Type w) (CEPosts : Type w₁) (AEPosts : Type w₂)
    (ERels : outParam (Type u)) [Assertion CPred] [Assertion APred] [Assertion CEPosts]
    [Assertion ERels] where
  /-- The concrete exception postconditions for the exception relation `E` and the abstract exception
  postconditions `Ea`. -/
  ePosts : Concretization CPred APred → ERels → AEPosts → CEPosts
  /-- The concrete exception postconditions grow with the exception relation. -/
  ePosts_mono (γ : Concretization CPred APred) {E E' : ERels} (Ea : AEPosts) :
    E ⊑ E' → ePosts γ E Ea ⊑ ePosts γ E' Ea

/-- The concretization of the exception postconditions of an aligned layer whose predicates have
the types `P` and `P'`, for the concretization `γ` of the programs. -/
class LayerConcretization (CPred APred : Type w) (P P' : Type w₁) [Assertion CPred] [Assertion APred]
    [Assertion P] [Assertion P'] where
  layer : Concretization CPred APred → Concretization P P'

instance {CPred APred : Type w} [Assertion CPred] [Assertion APred] :
    LayerConcretization CPred APred CPred APred where
  layer γ := γ

instance (priority := low) {CPred APred : Type w} {P : Type w₁} [Assertion CPred] [Assertion APred]
    [Assertion P] : LayerConcretization CPred APred P P where
  layer _ := Concretization.id P

namespace EPostsConcretization

variable {CPred APred : Type w} [Assertion CPred] [Assertion APred]

instance : EPostsConcretization CPred APred EStack⟨⟩ EStack⟨⟩ EStack⟨⟩ where
  ePosts _ _ _ := estack⟨⟩
  ePosts_mono _ _ _ _ _ := PartialOrder.rel_refl

noncomputable instance {εc εa : Type u} :
    EPostsConcretization CPred APred (εc → CPred) (εa → APred) (εc → εa → CPred) where
  ePosts γ R Ea := γ.post R Ea
  ePosts_mono γ _ _ Ea h := γ.post_mono Ea h

instance {εc : Type u} {P : Type w₁} [Assertion P] :
    EPostsConcretization CPred APred (εc → P) EStack⟨⟩ (εc → P) where
  ePosts _ E _ := E
  ePosts_mono _ _ _ _ h := h

noncomputable instance {εc εa : Type u} {P P' : Type w₁} {C : Type v₁} {A : Type v₂}
    {ERels : Type v₃} [Assertion P] [Assertion P'] [LayerConcretization CPred APred P P']
    [Assertion C] [Assertion ERels] [EPostsConcretization CPred APred C A ERels] :
    EPostsConcretization CPred APred ((εc → P) × C) ((εa → P') × A) ((εc → εa → P) × ERels) where
  ePosts γ E Ea :=
    ((LayerConcretization.layer γ).post E.1 Ea.1, EPostsConcretization.ePosts γ E.2 Ea.2)
  ePosts_mono γ _ _ Ea h :=
    ⟨(LayerConcretization.layer γ).post_mono Ea.1 h.1, EPostsConcretization.ePosts_mono γ Ea.2 h.2⟩

instance (priority := low) {εc : Type u} {P : Type w₁} {C : Type v₁} {A : Type v₂}
    {ERels : Type v₃} [Assertion P] [Assertion C] [Assertion ERels]
    [EPostsConcretization CPred APred C A ERels] :
    EPostsConcretization CPred APred ((εc → P) × C) A ((εc → P) × ERels) where
  ePosts γ E Ea := (E.1, EPostsConcretization.ePosts γ E.2 Ea)
  ePosts_mono γ _ _ Ea h := ⟨h.1, EPostsConcretization.ePosts_mono γ Ea h.2⟩

@[simp, grind norm] theorem ePosts_nil (γ : Concretization CPred APred) (E Ea : EStack⟨⟩) :
    ePosts γ E Ea = estack⟨⟩ := rfl

@[simp, grind norm] theorem ePosts_fun {εc εa : Type u} (γ : Concretization CPred APred)
    (R : εc → εa → CPred) (Ea : εa → APred) :
    ePosts γ R Ea = γ.post R Ea := rfl

@[simp, grind norm] theorem ePosts_fill {εc : Type u} {P : Type w₁} [Assertion P]
    (γ : Concretization CPred APred) (E : εc → P) (Ea : EStack⟨⟩) :
    ePosts γ E Ea = E := rfl

@[simp, grind norm] theorem ePosts_cons {εc εa : Type u} {C : Type v₁} {A : Type v₂} {ERels : Type v₃}
    [Assertion C] [Assertion ERels] [EPostsConcretization CPred APred C A ERels] (γ : Concretization CPred APred)
    (E : (εc → εa → CPred) × ERels) (Ea : (εa → APred) × A) :
    ePosts (CEPosts := (εc → CPred) × C) γ E Ea = (γ.post E.1 Ea.1, ePosts γ E.2 Ea.2) := rfl

@[simp, grind norm] theorem ePosts_cons_layer {εc εa : Type u} {P P' : Type w₁} {C : Type v₁}
    {A : Type v₂} {ERels : Type v₃} [Assertion P] [Assertion P'] [LayerConcretization CPred APred P P']
    [Assertion C] [Assertion ERels] [EPostsConcretization CPred APred C A ERels]
    (γ : Concretization CPred APred) (E : (εc → εa → P) × ERels) (Ea : (εa → P') × A) :
    ePosts (CEPosts := (εc → P) × C) γ E Ea =
      ((LayerConcretization.layer γ).post E.1 Ea.1, ePosts γ E.2 Ea.2) := rfl

@[simp, grind norm] theorem layer_self (γ : Concretization CPred APred) :
    LayerConcretization.layer (P := CPred) (P' := APred) γ = γ := rfl

@[simp, grind norm] theorem ePosts_cons_fill {εc : Type u} {P : Type w₁} {C : Type v₁} {A : Type v₂}
    {ERels : Type v₃} [Assertion P] [Assertion C] [Assertion ERels]
    [EPostsConcretization CPred APred C A ERels] (γ : Concretization CPred APred)
    (E : (εc → P) × ERels) (Ea : A) :
    ePosts (CEPosts := (εc → P) × C) γ E Ea = (E.1, ePosts γ E.2 Ea) := rfl

end EPostsConcretization

end Distillery
