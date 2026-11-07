import Ascent.Refinement
import Ascent.UB
import Ascent.Tactic.VCGen.Frontend

/-!
# Guarded word abstraction: the first synthesis family

The scaling family for ascend: a chain of `n` dependent `UInt64` additions in `Id` is abstracted
to a guarded `Int` chain in `UB`, related by `⌜wordVal · = ·⌝`. The synthesized program differs
structurally from the concrete one: each addition acquires a no-overflow guard that rides in the
abstract program and is threaded by `wp`. This is AutoCorres' word-abstraction phase in
miniature, built from `bind`/`pure`/leaf rules only.

The engine uses the fixed-relation specs `refines_addW` and `refines_pureW`: after each step the
engine introduces the related values as free variables, and the continuation hole of each bind
is applied to the abstract one. `wrp_bind` is the bind rule.
-/

open Std.WP Lean.Order Ascent

namespace AscendBench

def wordVal : UInt64 → Int := fun w => (w.toNat : Int)

/-- The word-abstraction phase: propositional assertions on both sides. -/
def γw : Concretization Prop Prop := Concretization.id Prop

/-- Adding a word to a related value is abstracted by the guarded integer sum. Registry form:
Q-generalized, so the spec applies to any return relation by unification. The precondition
carries the synthesis directives and the relation bookkeeping: `wordVal cv = av` pins the abstract input,
and the continuation receives the no-overflow guard and the *established* relation of the sum
as hypotheses, so downstream relation obligations close by assumption instead of re-deriving
the chain's arithmetic. -/
theorem addW_spec (av : Int) (cv y : UInt64) {Q : UInt64 → Int → Prop} {E : EStack⟨⟩} :
    ⦃(wordVal cv = av ∧
        (av + wordVal y < 2 ^ 64 → wordVal (cv + y) = av + wordVal y →
          Q (cv + y) (av + wordVal y)) : Prop)⦄
      (pure (cv + y) : Id UInt64)
      ⪯[γw] ((do UB.assume (av + wordVal y < 2 ^ 64); pure (av + wordVal y))) ⦃Q; E⦄ := by
  refine Refinement.assume_pure _ _ fun hovf hp => hp.2 hovf ?_
  obtain ⟨hav, -⟩ := hp
  subst hav
  show wordVal (cv + y) = wordVal cv + wordVal y
  have h : cv.toNat + y.toNat < 2 ^ 64 := by simp only [wordVal] at hovf; omega
  simp only [wordVal, UInt64.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-- The fixed-relation form of `addW_spec`, for the hand-written baseline chain: under the
no-overflow guard, the sum stays related. -/
@[ascend] theorem refines_addW (av : Int) (cv y : UInt64) {E : EStack⟨⟩} :
    ⦃(⌜wordVal cv = av⌝ : Prop)⦄
      (pure (cv + y) : Id UInt64)
      ⪯[γw] ((do UB.assume (av + wordVal y < 2 ^ 64); pure (av + wordVal y))) ⦃(⌜wordVal · = ·⌝); E⦄ := by
  refine (addW_spec av cv y).weaken ?_
  simp only [CompleteLattice.ofProp_prop_eq]
  intro hav
  exact ⟨hav, fun _ hcpl => hcpl⟩

/-- A pure word value is abstracted by its integer image. -/
theorem pureW_spec (cv : UInt64) {Q : UInt64 → Int → Prop} {E : EStack⟨⟩} :
    ⦃Q cv (wordVal cv)⦄ (pure cv : Id UInt64) ⪯[γw] (pure (wordVal cv) : UB Int) ⦃Q; E⦄ :=
  Refinement.pure _ _

/-- The fixed-relation form of `pureW_spec`: the seed of every chain. -/
@[ascend] theorem refines_pureW (cv : UInt64) {E : EStack⟨⟩} :
    ⦃(⊤ : Prop)⦄ (pure cv : Id UInt64) ⪯[γw] (pure (wordVal cv) : UB Int)
      ⦃(⌜wordVal · = ·⌝); E⦄ :=
  Refinement.pure_eq (f := wordVal) ⊤ cv rfl

attribute [ascend] wrp_bind

/-- The intermediate-relation bind form for the baseline chain: the head establishes `R`, the
continuations correspond under it. -/
theorem bindChain {CM AM : Type w → Type v} {CPred APred : Type w}
    {CEPosts AEPosts : Type w'} {ERels : Type u}
    [Monad CM] [Monad AM]
    [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
    [WPMonad CM CPred CEPosts] [WPMonad AM APred AEPosts] [WPMonadExact AM APred AEPosts]
    [EPostsConcretization CPred APred CEPosts AEPosts ERels]
    {γ : Concretization CPred APred}
    [Heyting CPred] {CV AV CV₂ AV₂ : Type w} {P : CPred}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {R : CV → AV → CPred} {Q : CV₂ → AV₂ → CPred} {E : ERels}
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
noncomputable def chainA (c : UInt64) : Nat → UB Int
  | 0 => pure (wordVal c)
  | n+1 => do let r ← chainA c n; (do UB.assume (r + wordVal c < 2 ^ 64); pure (r + wordVal c))

end AscendBench
