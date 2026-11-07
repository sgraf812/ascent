import Ascent.Concretization

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
-/

open Std.WP Lean.Order

namespace Ascent

universe u v₁ v₂ v₃ w w₁ w₂

/-- Computes the type `ERels` of exception relations between the exception stacks `CEPosts`
and `AEPosts`, and the concrete exception postconditions for an exception relation. -/
class EPostsConcretization (CPred APred : Type w) (CEPosts : Type w₁) (AEPosts : Type w₂)
    (ERels : outParam (Type u)) [Assertion CPred] [Assertion APred] where
  /-- The concrete exception postconditions for the exception relation `E` and the abstract exception
  postconditions `Ea`. -/
  ePosts : Concretization CPred APred → ERels → AEPosts → CEPosts

namespace EPostsConcretization

variable {CPred APred : Type w} [Assertion CPred] [Assertion APred]

instance : EPostsConcretization CPred APred EStack⟨⟩ EStack⟨⟩ EStack⟨⟩ where
  ePosts _ _ _ := estack⟨⟩

noncomputable instance {εc εa : Type u} :
    EPostsConcretization CPred APred (εc → CPred) (εa → APred) (εc → εa → CPred) where
  ePosts γ R Ea := γ.post R Ea

instance {εc : Type u} : EPostsConcretization CPred APred (εc → CPred) EStack⟨⟩ (εc → CPred) where
  ePosts _ E _ := E

noncomputable instance {εc εa : Type u} {C : Type v₁} {A : Type v₂} {ERels : Type v₃}
    [EPostsConcretization CPred APred C A ERels] :
    EPostsConcretization CPred APred ((εc → CPred) × C) ((εa → APred) × A)
      ((εc → εa → CPred) × ERels) where
  ePosts γ E Ea := (γ.post E.1 Ea.1, EPostsConcretization.ePosts γ E.2 Ea.2)

instance (priority := low) {εc : Type u} {C : Type v₁} {A : Type v₂} {ERels : Type v₃}
    [EPostsConcretization CPred APred C A ERels] :
    EPostsConcretization CPred APred ((εc → CPred) × C) A ((εc → CPred) × ERels) where
  ePosts γ E Ea := (E.1, EPostsConcretization.ePosts γ E.2 Ea)

@[simp, grind norm] theorem ePosts_nil (γ : Concretization CPred APred) (E Ea : EStack⟨⟩) :
    ePosts γ E Ea = estack⟨⟩ := rfl

@[simp, grind norm] theorem ePosts_fun {εc εa : Type u} (γ : Concretization CPred APred)
    (R : εc → εa → CPred) (Ea : εa → APred) :
    ePosts γ R Ea = γ.post R Ea := rfl

@[simp, grind norm] theorem ePosts_fill {εc : Type u} (γ : Concretization CPred APred)
    (E : εc → CPred) (Ea : EStack⟨⟩) :
    ePosts γ E Ea = E := rfl

@[simp, grind norm] theorem ePosts_cons {εc εa : Type u} {C : Type v₁} {A : Type v₂} {ERels : Type v₃}
    [EPostsConcretization CPred APred C A ERels] (γ : Concretization CPred APred)
    (E : (εc → εa → CPred) × ERels) (Ea : (εa → APred) × A) :
    ePosts (CEPosts := (εc → CPred) × C) γ E Ea = (γ.post E.1 Ea.1, ePosts γ E.2 Ea.2) := rfl

@[simp, grind norm] theorem ePosts_cons_fill {εc : Type u} {C : Type v₁} {A : Type v₂} {ERels : Type v₃}
    [EPostsConcretization CPred APred C A ERels] (γ : Concretization CPred APred)
    (E : (εc → CPred) × ERels) (Ea : A) :
    ePosts (CEPosts := (εc → CPred) × C) γ E Ea = (E.1, ePosts γ E.2 Ea) := rfl

end EPostsConcretization

end Ascent
