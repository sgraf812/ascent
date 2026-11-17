import DistilleryTests.WordAbsEngine

open Std.WP Lean.Order Distillery WordAbsEngine

namespace DistillUnfold

def chainC (c : UInt64) : Nat → Id UInt64
  | 0 => pure c
  | n+1 => do let r ← chainC c n; pure (r + c)

noncomputable def chainA (c : UInt64) : Nat → Demonic Int
  | 0 => (do Demonic.assert True; pure (wordVal c))
  | n+1 => do
    let r ← chainA c n
    (do Demonic.assert (r + wordVal c < 2 ^ 64); pure (r + wordVal c))

/-- `distill [chainC]` unfolds the recursive concrete program at a literal depth. -/
noncomputable def chain3 :
    { a : Demonic Int // ⦃(⊤ : Prop)⦄ (chainC 7 3) ⪯[γw] a ⦃(⌜FunRel wordVal · ·⌝)⦄ } := by
  apply Subtype.mk
  distill [chainC]

example : chain3.1 = chainA 7 3 := rfl

end DistillUnfold
