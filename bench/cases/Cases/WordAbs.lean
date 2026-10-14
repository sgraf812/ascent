import Ascent.Corres.Refinement
import Ascent.UB
import Ascend

/-!
# Guarded word abstraction: the first synthesis family

The scaling family for ascend: a chain of `n` dependent `UInt64` additions in `Id` is abstracted
to a guarded `Int` chain in `UB`, coupled by `⌜wordVal · = ·⌝`. The synthesized program differs
structurally from the concrete one: each addition acquires a no-overflow guard that rides in the
abstract program and is threaded by `wp`. This is AutoCorres' word-abstraction phase in
miniature, built from `bind`/`pure`/leaf rules only.

The registry form `addW_spec` is Q-generalized: it applies to any coupling by unification, so
the goal's rebound continuation rides through untouched (auto-framing). Its precondition carries
the synthesis directives: the coupling conjunct `wordVal cv = av` pins the abstract input to the
previously coupled value, and the guard sits as a hypothesis of the continuation. The coupling
form `refines_addW` used by the hand-written baseline chain derives from it by weakening.
-/

open Std.WP Lean.Order Ascent

namespace AscendBench

def wordVal : UInt64 → Int := fun w => (w.toNat : Int)

/-- The word-abstraction phase: propositional assertions on both sides. -/
def γw : Concretization Prop Prop EStack⟨⟩ EStack⟨⟩ := Concretization.id Prop EStack⟨⟩

/-- Adding a word to a coupled value is abstracted by the guarded integer sum. Registry form:
Q-generalized, so the spec applies to any coupling by unification. The precondition carries the
synthesis directives and the coupling bookkeeping: `wordVal cv = av` pins the abstract input,
and the continuation receives the no-overflow guard and the *established* coupling of the sum
as hypotheses, so downstream coupling obligations close by assumption instead of re-deriving
the chain's arithmetic. -/
@[ascend] theorem addW_spec (av : Int) (cv y : UInt64) {Q : UInt64 → Int → Prop} {E : EStack⟨⟩} :
    ⦃(wordVal cv = av ∧
        (av + wordVal y < 2 ^ 64 → wordVal (cv + y) = av + wordVal y →
          Q (cv + y) (av + wordVal y)) : Prop)⦄
      (pure (cv + y) : Id UInt64)
      ⪯[γw] (UB.guardRet (av + wordVal y < 2 ^ 64) (av + wordVal y)) ⦃Q; E⦄ := by
  refine Refinement.guardRet _ _ fun hovf hp => hp.2 hovf ?_
  obtain ⟨hav, -⟩ := hp
  subst hav
  show wordVal (cv + y) = wordVal cv + wordVal y
  have h : cv.toNat + y.toNat < 2 ^ 64 := by simp only [wordVal] at hovf; omega
  simp only [wordVal, UInt64.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-- The coupling form of `addW_spec`, for the hand-written baseline chain: under the no-overflow
guard, the sum stays coupled. -/
theorem refines_addW (av : Int) (cv y : UInt64) :
    ⦃(⌜wordVal cv = av⌝ : Prop)⦄
      (pure (cv + y) : Id UInt64)
      ⪯[γw] (UB.guardRet (av + wordVal y < 2 ^ 64) (av + wordVal y)) ⦃(⌜wordVal · = ·⌝)⦄ := by
  refine (addW_spec av cv y).weaken ?_
  simp only [CompleteLattice.ofProp_prop_eq]
  intro hav
  exact ⟨hav, fun _ hcpl => hcpl⟩

/-- A pure word value is abstracted by its integer image. Registry form; the seed of every
chain. -/
@[ascend] theorem pureW_spec (cv : UInt64) {Q : UInt64 → Int → Prop} {E : EStack⟨⟩} :
    ⦃Q cv (wordVal cv)⦄ (pure cv : Id UInt64) ⪯[γw] (pure (wordVal cv) : UB Int) ⦃Q; E⦄ :=
  Refinement.pure _ _

/-- The mid-coupling bind form for the baseline chain: the head establishes `R`, the
continuations correspond under it. -/
theorem bindChain {CM AM : Type w → Type v} {CPred APred : Type w}
    {CEPred AEPred : Type w'} {Ξ : Type u}
    [Monad CM] [Monad AM]
    [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
    [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] [WPMonadExact AM APred AEPred]
    [HasEPost CPred APred CEPred AEPred Ξ]
    {γ : Concretization CPred APred CEPred AEPred}
    [Heyting CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {R : CV → AV → CPred} {Q : CV₂ → AV₂ → CPred} {E : Ξ}
    (h₁ : ⦃P⦄ c₁ ⪯[γ] a₁ ⦃R; E⦄)
    (h₂ : ∀ cv av, ⦃R cv av⦄ (c₂ cv) ⪯[γ] (a₂ av) ⦃Q; E⦄) :
    ⦃P⦄ (c₁ >>= c₂) ⪯[γ] (a₁ >>= a₂) ⦃Q; E⦄ :=
  Refinement.bind.weaken
    (PartialOrder.rel_trans h₁.le_wrp (wrp_mono_post fun cv av => (h₂ cv av).le_wrp))

/-- The concrete chain: `n` dependent additions of the constant `c`. -/
def chainC (c : UInt64) : Nat → Id UInt64
  | 0 => pure c
  | n+1 => do let r ← chainC c n; pure (r + c)

/-- The expected abstract image of `chainC`: the guarded integer chain, for the golden check. -/
def chainA (c : UInt64) : Nat → UB Int
  | 0 => pure (wordVal c)
  | n+1 => do let r ← chainA c n; UB.guardRet (r + wordVal c < 2 ^ 64) (r + wordVal c)

end AscendBench
