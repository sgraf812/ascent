import Ascent.Corres.Sim

/-!
# Word abstraction: `UInt64 ↝ Int`

Machine-word values are abstracted to mathematical integers. The assertion lattice is
unchanged, so the concretization is `Concretization.id`; the abstraction lives entirely in the
value coupling `⌜· = wordVal ·⌝`, supplied per triple. Each arithmetic simulation is an
instance of `SimTriple.pure_eq` whose value-equality hypothesis is the no-overflow
side-condition, discharged by `omega`. A genuinely overflowing program admits no simulation.
-/

open Std.Internal.Do Lean.Order Ascent

/-- The value abstraction underlying word abstraction. -/
def wordVal : UInt64 → Int := fun w => (w.toNat : Int)

/-- The word-abstraction concretization on pure computations: identity on assertions. -/
def wordAbstraction : Concretization Prop Prop EPost.Nil EPost.Nil :=
  Concretization.id Prop EPost.Nil


/-- Addition abstracts to integer addition when it does not overflow. -/
example (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) :
    ⦃(⊤ : Prop)⦄ (pure (wordVal a + wordVal b) : Id Int)
      ⊑[wordAbstraction] (pure (a + b) : Id UInt64) ⦃(⌜· = wordVal ·⌝); ()⦄ := by
  refine .pure_eq ⊤ _ ?_
  show wordVal (a + b) = wordVal a + wordVal b
  simp only [wordVal, UInt64.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-- Multiplication abstracts to integer multiplication when it does not overflow. -/
example (a b : UInt64) (h : a.toNat * b.toNat < 2 ^ 64) :
    ⦃(⊤ : Prop)⦄ (pure (wordVal a * wordVal b) : Id Int)
      ⊑[wordAbstraction] (pure (a * b) : Id UInt64) ⦃(⌜· = wordVal ·⌝); ()⦄ := by
  refine .pure_eq ⊤ _ ?_
  show wordVal (a * b) = wordVal a * wordVal b
  simp only [wordVal, UInt64.toNat_mul, Nat.mod_eq_of_lt h]
  rfl

/-- Subtraction abstracts to integer subtraction when it does not underflow (`b ≤ a`). -/
example (a b : UInt64) (h : b ≤ a) :
    ⦃(⊤ : Prop)⦄ (pure (wordVal a - wordVal b) : Id Int)
      ⊑[wordAbstraction] (pure (a - b) : Id UInt64) ⦃(⌜· = wordVal ·⌝); ()⦄ := by
  refine .pure_eq ⊤ _ ?_
  show wordVal (a - b) = wordVal a - wordVal b
  have hle : b.toNat ≤ a.toNat := h
  simp only [wordVal, UInt64.toNat_sub_of_le _ _ h]
  omega

/-- A genuinely overflowing addition has no word abstraction: the no-overflow equation that
`SimTriple.pure_eq` would demand is false, since `2^63 + 2^63` wraps to `0`. -/
example : wordVal (2 ^ 63) + wordVal (2 ^ 63) ≠ wordVal ((2 ^ 63) + (2 ^ 63) : UInt64) := by
  native_decide

/-- Simulation chains through the `Trans` instance: `SimTriple.refl` is the identity and
composition is transitivity. -/
example {Prog Val : Type} [WP Prog Val Prop EPost.Nil] (x : Prog) :
    ⦃(⊤ : Prop)⦄ x
      ⊑[(Concretization.id Prop EPost.Nil).comp (Concretization.id Prop EPost.Nil)] x
      ⦃fun (av cv : Val) => ⌜av = cv⌝; ()⦄ :=
  Trans.trans (SimTriple.refl ⊤ x) (SimTriple.refl ⊤ x)
