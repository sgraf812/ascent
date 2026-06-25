import Ascent.Corres.Basic

/-!
# Word abstraction: `UInt64 ↝ Int`

Machine-word values are abstracted to mathematical integers. The assertion lattice is
unchanged, so the refinement is `idRefinement`; the abstraction lives entirely in the value
map `wordαV`, supplied per `Corres`. Each arithmetic correspondence is an instance of
`corres_pure` whose value-equality hypothesis is the no-overflow side-condition, discharged by
`omega`. A genuinely overflowing program admits no correspondence.
-/

open Std.Internal.Do Lean.Order Ascent

/-- The value abstraction underlying word abstraction. -/
def wordαV : UInt64 → Int := fun w => (w.toNat : Int)

/-- The word-abstraction refinement on pure computations: identity on assertions. -/
def wordAbstraction : Refinement Prop Prop EPost.Nil EPost.Nil :=
  idRefinement Prop EPost.Nil

instance : LawfulRefinement wordAbstraction Id Id where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun _ _ _ _ => PartialOrder.rel_refl

/-- Addition abstracts to integer addition when it does not overflow. -/
example (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) :
    Corres wordAbstraction ⊤ (αVeq wordαV)
      (pure (wordαV a + wordαV b) : Id Int) (pure (a + b) : Id UInt64) := by
  apply corres_pure ⊤
  show wordαV (a + b) = wordαV a + wordαV b
  simp only [wordαV, UInt64.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-- Multiplication abstracts to integer multiplication when it does not overflow. -/
example (a b : UInt64) (h : a.toNat * b.toNat < 2 ^ 64) :
    Corres wordAbstraction ⊤ (αVeq wordαV)
      (pure (wordαV a * wordαV b) : Id Int) (pure (a * b) : Id UInt64) := by
  apply corres_pure ⊤
  show wordαV (a * b) = wordαV a * wordαV b
  simp only [wordαV, UInt64.toNat_mul, Nat.mod_eq_of_lt h]
  rfl

/-- Subtraction abstracts to integer subtraction when it does not underflow (`b ≤ a`). -/
example (a b : UInt64) (h : b ≤ a) :
    Corres wordAbstraction ⊤ (αVeq wordαV)
      (pure (wordαV a - wordαV b) : Id Int) (pure (a - b) : Id UInt64) := by
  apply corres_pure ⊤
  show wordαV (a - b) = wordαV a - wordαV b
  have hle : b.toNat ≤ a.toNat := h
  simp only [wordαV, UInt64.toNat_sub_of_le _ _ h]
  omega

/-- A genuinely overflowing addition has no word abstraction: the no-overflow equation that
`corres_pure` would demand is false, since `2^63 + 2^63` wraps to `0`. -/
example : wordαV (2 ^ 63) + wordαV (2 ^ 63) ≠ wordαV ((2 ^ 63) + (2 ^ 63) : UInt64) := by
  native_decide

/-- Correspondence chains through the `Trans` instance: `corres_id` is the identity and
composition is transitivity. -/
example {Prog Val : Type} [WP Prog Val Prop EPost.Nil] (x : Prog) :
    Corres ((idRefinement Prop EPost.Nil).comp (idRefinement Prop EPost.Nil))
      ⊤ (αVeq (id ∘ id : Val → Val)) x x :=
  Trans.trans (corres_id ⊤ x) (corres_id ⊤ x)
