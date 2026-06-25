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
    Corres (Concretization.id Prop EPost.Nil) ⊤ (αVeq wordαV)
      (do let r ← pure (wordαV a + wordαV b)
          UB.guardRet (r * wordαV c < 2 ^ 64) (r * wordαV c) : UB Int)
      (do let r ← pure (a + b); pure (r * c) : Id UInt64) := by
  refine corres_bind_top wordαV wordαV ?_ (fun cv => ?_)
  · apply corres_pure ⊤
    show wordαV (a + b) = wordαV a + wordαV b
    simp only [wordαV, UInt64.toNat_add, Nat.mod_eq_of_lt h1]
    omega
  · apply corres_guardRet ⊤
    intro hovf
    show wordαV (cv * c) = wordαV cv * wordαV c
    have hlt : cv.toNat * c.toNat < 2 ^ 64 := by
      simp only [wordαV] at hovf; omega
    simp only [wordαV, UInt64.toNat_mul, Nat.mod_eq_of_lt hlt]
    rfl
