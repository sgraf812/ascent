import Distillery.PureRefinement
import Distillery.Demonic
import Distillery.Tactic.VCGen.Frontend

/-!
# Guarded word abstraction through `@[distill_pure]` rules

The family of `Cases.WordAbs`: a chain of `n` dependent `UInt64` additions in `Id` abstracts to a
guarded `Int` chain in `Demonic`, related by `FunRel wordVal`. `Refinement.pure_rel` abstracts each
`pure`, and the rules `abs_add` and `abs_wordVal` abstract the value inside it. `chainC` unfolds to
a left-nested chain of binds, and `wrp_bind_assoc` reassociates it to the right, so the abstract
program is the right-nested `chainA`.
-/

open Std.WP Lean.Order Distillery

namespace DistillBenchVal

def wordVal : UInt64 → Int := fun w => (w.toNat : Int)

abbrev γw : Concretization Prop Prop := Concretization.id Prop

attribute [distill] wrp_bind Refinement.pure_rel
attribute [distill default + 1] wrp_bind_assoc
attribute [distill] wrp_kleisli

@[distill_pure] theorem abs_add {a b : UInt64} {x y : Int} {P₁ P₂ : Prop}
    (h₁ : PureRefinement a x P₁ (FunRel wordVal)) (h₂ : PureRefinement b y P₂ (FunRel wordVal)) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂ ∧ x + y < 2 ^ 64) (FunRel wordVal) := by
  intro ⟨hP₁, hP₂, h⟩
  have ha := h₁ hP₁
  have hb := h₂ hP₂
  simp only [funRel_iff, wordVal] at ha hb h ⊢
  subst ha hb
  have h' : a.toNat + b.toNat < 2 ^ 64 := by omega
  simp only [UInt64.toNat_add, Nat.mod_eq_of_lt h']
  omega

@[distill_pure low] theorem abs_wordVal {c : UInt64} :
    PureRefinement c (wordVal c) True (FunRel wordVal) :=
  PureRefinement.funRel

def chainC (c : UInt64) : Nat → Id UInt64
  | 0 => pure c
  | n+1 => do let r ← chainC c n; pure (r + c)

noncomputable def chainASteps (c : UInt64) : Int → Nat → Demonic Int
  | acc, 0 => (do Demonic.assert (acc + wordVal c < 2 ^ 64); pure (acc + wordVal c))
  | acc, n+1 => do let r ← (do Demonic.assert (acc + wordVal c < 2 ^ 64); pure (acc + wordVal c)); chainASteps c r n

noncomputable def chainA (c : UInt64) : Nat → Demonic Int
  | 0 => (do Demonic.assert True; pure (wordVal c))
  | n+1 => do let r ← (do Demonic.assert True; pure (wordVal c)); chainASteps c r n

def chainCR (c : UInt64) : UInt64 → Nat → Id UInt64
  | acc, 0 => pure acc
  | acc, n+1 => do let r ← pure (acc + c); chainCR c r n

noncomputable def chainAR (c : UInt64) : Int → Nat → Demonic Int
  | acc, 0 => (do Demonic.assert True; pure acc)
  | acc, n+1 => do let r ← (do Demonic.assert (acc + wordVal c < 2 ^ 64); pure (acc + wordVal c)); chainAR c r n

end DistillBenchVal
