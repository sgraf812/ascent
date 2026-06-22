import Ascent.Corres.Basic

/-!
# Word abstraction: `UInt64 ↝ Int`

Machine-word values are abstracted to mathematical integers. The assertion lattice is
unchanged, so the refinement is `idRefinement`; the abstraction lives entirely in the value
map `wordγV`, supplied per `Corres`. Each arithmetic correspondence is an instance of
`corres_pure` whose value-equality hypothesis is the no-overflow side-condition, discharged by
`omega`. A genuinely overflowing program admits no correspondence.
-/

open Std.Internal.Do Lean.Order Ascent

/-- The value abstraction underlying word abstraction. -/
def wordγV : UInt64 → Int := fun w => (w.toNat : Int)

/-- The word-abstraction refinement on pure computations: identity on assertions. -/
def wordAbstraction : Refinement Prop Prop EPost.Nil EPost.Nil :=
  idRefinement Prop EPost.Nil

instance : LawfulRefinement wordAbstraction Id Id :=
  .ofWPMorphism (fun _ _ _ => PartialOrder.rel_refl) (fun _ _ _ _ => PartialOrder.rel_refl)

/-- Addition abstracts to integer addition when it does not overflow. -/
example (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) :
    Corres wordAbstraction wordγV
      (pure (wordγV a + wordγV b) : Id Int) (pure (a + b) : Id UInt64) := by
  apply corres_pure
  show wordγV (a + b) = wordγV a + wordγV b
  simp only [wordγV, UInt64.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-- A genuinely overflowing addition has no word abstraction: the no-overflow equation that
`corres_pure` would demand is false, since `2^63 + 2^63` wraps to `0`. -/
example : wordγV (2 ^ 63) + wordγV (2 ^ 63) ≠ wordγV ((2 ^ 63) + (2 ^ 63) : UInt64) := by
  native_decide

/-- Correspondence chains through the `Trans` instance: `corres_id` is the identity and
composition is transitivity. -/
example {Prog Val : Type} [WP Prog Val Prop EPost.Nil] (x : Prog) :
    Corres ((idRefinement Prop EPost.Nil).comp (idRefinement Prop EPost.Nil))
      (id ∘ id : Val → Val) x x :=
  Trans.trans (corres_id x) (corres_id x)
