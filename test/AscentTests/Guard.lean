import Ascent.UB
import AscentTests.WordAbstraction

/-!
# Guards: value-dependent side-conditions through `UB`

A demo of the `UB` guard effect (`Ascent.UB`): the word-overflow `bind` that could not be related
unconditionally now goes through, because the no-overflow obligation rides inside the abstract
program as a guard and is threaded by `wp`. On bad values the abstract program fails (`wp = ⊥`),
discharging the correspondence trivially.
-/

open Std.Internal.Do Lean.Order Ascent

/-- The word-overflow `bind` that was impossible without guards: a second operation whose overflow
depends on the first operation's *result*. The continuation guards on no-overflow, so the
correspondence holds for every intermediate value. -/
example (a b c : UInt64) (h1 : a.toNat + b.toNat < 2 ^ 64) :
    Corres (Concretization.id Prop EPost.Nil) ⊤ (coupleEq wordVal)
      (do let r ← pure (wordVal a + wordVal b)
          UB.guardRet (r * wordVal c < 2 ^ 64) (r * wordVal c) : UB Int)
      (do let r ← pure (a + b); pure (r * c) : Id UInt64) := by
  refine corres_bind_top wordVal wordVal ?_ (fun cv => ?_)
  · apply corres_pure ⊤
    show wordVal (a + b) = wordVal a + wordVal b
    simp only [wordVal, UInt64.toNat_add, Nat.mod_eq_of_lt h1]
    omega
  · apply corres_guardRet ⊤
    intro hovf
    show wordVal (cv * c) = wordVal cv * wordVal c
    have hlt : cv.toNat * c.toNat < 2 ^ 64 := by
      simp only [wordVal] at hovf; omega
    simp only [wordVal, UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]
    rfl
