import AscentTests.WordAbsEngine

open Std.WP Lean.Order Ascent WordAbsEngine

namespace AscendUnfold

def chainC (c : UInt64) : Nat → Id UInt64
  | 0 => pure c
  | n+1 => do let r ← chainC c n; pure (r + c)

noncomputable def chainA (c : UInt64) : Nat → UB Int
  | 0 => (do UB.assume True; pure (wordVal c))
  | n+1 => do
    let r ← chainA c n
    (do UB.assume (r + wordVal c < 2 ^ 64); pure (r + wordVal c))

/-- `ascend [chainC]` unfolds the recursive concrete program at a literal depth. -/
noncomputable def chain3 :
    { a : UB Int // ⦃(⊤ : Prop)⦄ (chainC 7 3) ⪯[γw] a ⦃(⌜FunRel wordVal · ·⌝)⦄ } := by
  apply Subtype.mk
  ascend [chainC]

example : chain3.1 = chainA 7 3 := rfl

end AscendUnfold
