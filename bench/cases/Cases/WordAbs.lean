import Ascent.Corres.RTriple
import Ascent.UB

/-!
# Guarded word abstraction: the first synthesis family

The scaling family for ascend: a chain of `n` dependent `UInt64` additions in `Id` is abstracted
to a guarded `Int` chain in `UB`, coupled by `⌜· = wordVal ·⌝`. The synthesized program differs
structurally from the concrete one: each addition acquires a no-overflow guard that rides in the
abstract program and is threaded by `wp`. This is AutoCorres' word-abstraction phase in
miniature, built from `bind`/`pure`/leaf rules only.

The registry form `addW_spec` is Q-generalized: it applies to any coupling by unification, so
the goal's rebound continuation rides through untouched (auto-framing). Its precondition carries
the synthesis directives: the coupling conjunct `av = wordVal cv` pins the abstract input to the
previously coupled value, and the guard sits as a hypothesis of the continuation. The coupling
form `refines_addW` used by the hand-written baseline chain derives from it by weakening.
-/

open Std.Internal.Do Lean.Order Ascent

namespace AscendBench

def wordVal : UInt64 → Int := fun w => (w.toNat : Int)

/-- The word-abstraction phase: propositional assertions on both sides. -/
def γw : Concretization Prop Prop EPost.Nil EPost.Nil := Concretization.id Prop EPost.Nil

/-- Adding a word to a coupled value is abstracted by the guarded integer sum. Registry form:
Q-generalized, so the spec applies to any coupling by unification. The precondition carries the
synthesis directives: `av = wordVal cv` pins the abstract input, and the guard is a hypothesis
of the continuation. -/
theorem addW_spec (av : Int) (cv y : UInt64) {Q : Int → UInt64 → Prop} {E : EPost.Nil} :
    ⦃(av = wordVal cv ∧ (av + wordVal y < 2 ^ 64 → Q (av + wordVal y) (cv + y)) : Prop)⦄
      (UB.guardRet (av + wordVal y < 2 ^ 64) (av + wordVal y))
      ⊑[γw] (pure (cv + y) : Id UInt64) ⦃Q; E⦄ :=
  RTriple.guardRet _ _ fun hovf hp => hp.2 hovf

/-- The coupling form of `addW_spec`, for the hand-written baseline chain: under the no-overflow
guard, the sum stays coupled. -/
theorem refines_addW (av : Int) (cv y : UInt64) :
    ⦃(⌜av = wordVal cv⌝ : Prop)⦄
      (UB.guardRet (av + wordVal y < 2 ^ 64) (av + wordVal y))
      ⊑[γw] (pure (cv + y) : Id UInt64) ⦃(⌜· = wordVal ·⌝)⦄ := by
  refine (addW_spec av cv y).weaken ?_
  simp only [ofProp_prop_eq]
  intro hav
  refine ⟨hav, fun hovf => ?_⟩
  subst hav
  show wordVal cv + wordVal y = wordVal (cv + y)
  have h : cv.toNat + y.toNat < 2 ^ 64 := by simp only [wordVal] at hovf; omega
  simp only [wordVal, UInt64.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-- The concrete chain: `n` dependent additions of the constant `c`. -/
def chainC (c : UInt64) : Nat → Id UInt64
  | 0 => pure c
  | n+1 => do let r ← chainC c n; pure (r + c)

/-- The expected abstract image of `chainC`: the guarded integer chain, for the golden check. -/
def chainA (c : UInt64) : Nat → UB Int
  | 0 => pure (wordVal c)
  | n+1 => do let r ← chainA c n; UB.guardRet (r + wordVal c < 2 ^ 64) (r + wordVal c)

end AscendBench
