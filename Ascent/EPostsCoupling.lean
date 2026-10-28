import Ascent.Concretization

/-!
# Exception couplings

`Q : CVal → AVal → CPred` couples the values that a concrete and an abstract program return.
An exception coupling `E : Ξ` couples the values that they throw. `Ξ` mirrors the concrete
exception stack, one component per concrete layer:

| `CEPosts` | `AEPosts` | `Ξ` |
|---|---|---|
| `EStack⟨⟩` | `EStack⟨⟩` | `EStack⟨⟩` |
| `εc → CPred` | `εa → APred` | `εc → εa → CPred` |
| `εc → CPred` | `EStack⟨⟩` | `εc → CPred` |
| `(εc → CPred) × C` | `(εa → APred) × A` | `(εc → εa → CPred) × Ξ'` |
| `(εc → CPred) × C` | `A` | `(εc → CPred) × Ξ'` |

A layer that both programs have carries a relation `R`, and `R ec ea` states that the concrete
thrown value `ec` corresponds to the abstract thrown value `ea`. A layer that only the concrete
program has carries a postcondition on the concrete thrown values. Layers align from the
outside in.

`EPostsCoupling.ePosts γ E Ea` is the concrete exception postcondition for the abstract one `Ea`.
On an aligned layer it is `γ.post R`, as `γ.post Q` is on values.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v₁ v₂ v₃ w w₁ w₂

/-- Computes the type `Ξ` of exception couplings between the exception stacks `CEPosts` and
`AEPosts`, and the concrete exception postconditions for a coupling. -/
class EPostsCoupling (CPred APred : Type w) (CEPosts : Type w₁) (AEPosts : Type w₂)
    (Ξ : outParam (Type u)) [Assertion CPred] [Assertion APred] where
  /-- The concrete exception postconditions for the coupling `E` and the abstract exception
  postconditions `Ea`. -/
  ePosts : Concretization CPred APred → Ξ → AEPosts → CEPosts

namespace EPostsCoupling

variable {CPred APred : Type w} [Assertion CPred] [Assertion APred]

instance : EPostsCoupling CPred APred EStack⟨⟩ EStack⟨⟩ EStack⟨⟩ where
  ePosts _ _ _ := estack⟨⟩

noncomputable instance {εc εa : Type u} :
    EPostsCoupling CPred APred (εc → CPred) (εa → APred) (εc → εa → CPred) where
  ePosts γ R Ea := γ.post R Ea

instance {εc : Type u} : EPostsCoupling CPred APred (εc → CPred) EStack⟨⟩ (εc → CPred) where
  ePosts _ E _ := E

noncomputable instance {εc εa : Type u} {C : Type v₁} {A : Type v₂} {Ξ : Type v₃}
    [EPostsCoupling CPred APred C A Ξ] :
    EPostsCoupling CPred APred ((εc → CPred) × C) ((εa → APred) × A) ((εc → εa → CPred) × Ξ) where
  ePosts γ E Ea := (γ.post E.1 Ea.1, EPostsCoupling.ePosts γ E.2 Ea.2)

instance (priority := low) {εc : Type u} {C : Type v₁} {A : Type v₂} {Ξ : Type v₃}
    [EPostsCoupling CPred APred C A Ξ] :
    EPostsCoupling CPred APred ((εc → CPred) × C) A ((εc → CPred) × Ξ) where
  ePosts γ E Ea := (E.1, EPostsCoupling.ePosts γ E.2 Ea)

@[simp] theorem ePosts_nil (γ : Concretization CPred APred) (E Ea : EStack⟨⟩) :
    ePosts γ E Ea = estack⟨⟩ := rfl

@[simp] theorem ePosts_fun {εc εa : Type u} (γ : Concretization CPred APred)
    (R : εc → εa → CPred) (Ea : εa → APred) :
    ePosts γ R Ea = γ.post R Ea := rfl

@[simp] theorem ePosts_fill {εc : Type u} (γ : Concretization CPred APred)
    (E : εc → CPred) (Ea : EStack⟨⟩) :
    ePosts γ E Ea = E := rfl

@[simp] theorem ePosts_cons {εc εa : Type u} {C : Type v₁} {A : Type v₂} {Ξ : Type v₃}
    [EPostsCoupling CPred APred C A Ξ] (γ : Concretization CPred APred)
    (E : (εc → εa → CPred) × Ξ) (Ea : (εa → APred) × A) :
    ePosts (CEPosts := (εc → CPred) × C) γ E Ea = (γ.post E.1 Ea.1, ePosts γ E.2 Ea.2) := rfl

@[simp] theorem ePosts_cons_fill {εc : Type u} {C : Type v₁} {A : Type v₂} {Ξ : Type v₃}
    [EPostsCoupling CPred APred C A Ξ] (γ : Concretization CPred APred)
    (E : (εc → CPred) × Ξ) (Ea : A) :
    ePosts (CEPosts := (εc → CPred) × C) γ E Ea = (E.1, ePosts γ E.2 Ea) := rfl

end EPostsCoupling

end Ascent
