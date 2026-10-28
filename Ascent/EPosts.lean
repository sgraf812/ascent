import Ascent.Concretization

/-!
# Exception couplings

`wrp γ c a Q E` couples thrown values with `E`, as it couples returned values with `Q`. The
type `Ξ` of `E` depends on the exception stacks of the two programs. `HasEPost` reads `Ξ` off
the two stacks and turns `E` and the abstract exception postconditions into the concrete
exception postconditions.

Three cases:
* The abstract program throws nothing (`EStack⟨⟩`). Then `Ξ := EStack⟨⟩`, and `γ.ePosts`
  fills the concrete stack.
* One exception type on each side, as in `Except εc` and `Except εa`. Then
  `Ξ := εc → εa → CPred`, and `γ.post E` couples the thrown values.
* One exception layer on each side above further layers. `Ξ` is as in the second case.
  `γ.post E` couples the heads, and `γ.ePosts` transports the rest.
-/

open Std.WP Lean.Order

namespace Ascent

universe u w w'

/-- Reads the type `Ξ` of the exception coupling off the two exception stacks, and builds the
concrete exception postconditions from the coupling and the abstract ones. -/
class HasEPost (CPred APred : Type w) (CEPosts AEPosts : Type w') (Ξ : outParam (Type u))
    [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts] where
  /-- The concrete exception postconditions for the coupling `E` and the abstract exception
  postconditions `Ea`. -/
  ePosts : Concretization CPred APred CEPosts AEPosts → Ξ → AEPosts → CEPosts

instance {CPred APred : Type w} {CEPosts : Type} [Assertion CPred] [Assertion APred]
    [Assertion CEPosts] :
    HasEPost CPred APred CEPosts EStack⟨⟩ EStack⟨⟩ where
  ePosts γ _ := γ.ePosts

noncomputable instance {CPred APred : Type w} {εc εa : Type u}
    [Assertion CPred] [Assertion APred] :
    HasEPost CPred APred (εc → CPred) (εa → APred) (εc → εa → CPred) where
  ePosts γ E Ea := γ.post E Ea

noncomputable instance {CPred APred : Type w} {εc εa : Type u} {CRest ARest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CRest] [Assertion ARest] :
    HasEPost CPred APred ((εc → CPred) × CRest) ((εa → APred) × ARest) (εc → εa → CPred) where
  ePosts γ E Ea := (γ.post E Ea.1, (γ.ePosts Ea).2)

@[simp] theorem HasEPost.ePosts_nil {CPred APred : Type w} {CEPosts : Type}
    [Assertion CPred] [Assertion APred] [Assertion CEPosts]
    (γ : Concretization CPred APred CEPosts EStack⟨⟩) (E Ea : EStack⟨⟩) :
    HasEPost.ePosts γ E Ea = γ.ePosts Ea := rfl

@[simp] theorem HasEPost.ePosts_fun {CPred APred : Type w} {εc εa : Type u}
    [Assertion CPred] [Assertion APred]
    (γ : Concretization CPred APred (εc → CPred) (εa → APred))
    (E : εc → εa → CPred) (Ea : εa → APred) :
    HasEPost.ePosts γ E Ea = γ.post E Ea := rfl

@[simp] theorem HasEPost.ePosts_cons_head {CPred APred : Type w} {εc εa : Type u}
    {CRest ARest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CRest] [Assertion ARest]
    (γ : Concretization CPred APred ((εc → CPred) × CRest) ((εa → APred) × ARest))
    (E : εc → εa → CPred) (Ea : (εa → APred) × ARest) :
    (HasEPost.ePosts γ E Ea).1 = γ.post E Ea.1 := rfl

@[simp] theorem HasEPost.ePosts_cons_tail {CPred APred : Type w} {εc εa : Type u}
    {CRest ARest : Type w'}
    [Assertion CPred] [Assertion APred] [Assertion CRest] [Assertion ARest]
    (γ : Concretization CPred APred ((εc → CPred) × CRest) ((εa → APred) × ARest))
    (E : εc → εa → CPred) (Ea : (εa → APred) × ARest) :
    (HasEPost.ePosts γ E Ea).2 = (γ.ePosts Ea).2 := rfl

end Ascent
