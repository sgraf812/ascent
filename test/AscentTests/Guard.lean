import Ascent.UB
import AscentTests.TripleScaffold
import AscentTests.WordAbstraction

/-!
# Guards: value-dependent side-conditions through `UB`

A demo of the `UB` guard effect (`Ascent.UB`): the word-overflow `bind` that could not be related
unconditionally now goes through, because the no-overflow obligation rides inside the abstract
program as a guard and is threaded by `wp`. On bad values the abstract program fails (`wp = ⊥`),
discharging the refinement trivially.
-/

open Std.WP Lean.Order Ascent

/-- The word-overflow `bind` that was impossible without guards: a second operation whose overflow
depends on the first operation's *result*. The continuation guards on no-overflow, so the
refinement holds for every intermediate value. -/
example (a b c : UInt64) (h1 : a.toNat + b.toNat < 2 ^ 64) :
    ⦃(⊤ : Prop)⦄
      (do let r ← pure (a + b); pure (r * c) : Id UInt64)
      ⪯[Concretization.id Prop EStack⟨⟩]
      (do let r ← pure (wordVal a + wordVal b)
          UB.guardRet (r * wordVal c < 2 ^ 64) (r * wordVal c) : UB Int)
      ⦃(⌜wordVal · = ·⌝)⦄ := by
  refine .bind_eq (f := wordVal) (.pure_eq ⊤ _ ?_) fun cv => ?_
  · show wordVal (a + b) = wordVal a + wordVal b
    simp only [wordVal, UInt64.toNat_add, Nat.mod_eq_of_lt h1]
    omega
  · refine .guardRet _ _ fun hovf => CompleteLattice.le_ofProp _ _ ?_
    show wordVal (cv * c) = wordVal cv * wordVal c
    have hlt : cv.toNat * c.toNat < 2 ^ 64 := by
      simp only [wordVal] at hovf; omega
    simp only [wordVal, UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]
    rfl
