import Driver
import Cases.WordAbs

/-!
# Guarded word abstraction, baseline measurements

The baseline solver builds the rule-chain proof directly as a term (one `bindChain` per
concrete bind, `refines_addW` at each leaf, `RTriple.pure_eq` at the seed) and elaborates it
once with `exact`. It performs no search and no rule-database lookup, so it is the
speed-of-light reference for the ascend engine on this family: measured cost is elaboration,
unification, and kernel checking of the synthesized proof.
-/

open Lean Meta Elab Std.Internal.Do Lean.Order Ascent AscendBench

/-- The rule-chain proof for `chainC 7 n`, as a term. -/
partial def chainProofStx : Nat → MetaM Term
  | 0 => `(RTriple.pure_eq (f := wordVal) ⊤ _ rfl)
  | n+1 => do `(bindChain $(← chainProofStx n) fun av cv => refines_addW av cv _)

def mkStmt (n : Nat) : MetaM Term :=
  `(⦃(⊤ : Prop)⦄ (?_ : UB Int) ⊑[γw] (chainC 7 $(quote n)) ⦃(⌜· = wordVal ·⌝)⦄)

def mkExpected (n : Nat) : MetaM Term :=
  `(chainA 7 $(quote n))

def solveBaseline (n : Nat) (goal : MVarId) : MetaM (List MVarId × (Expr → Expr)) := do
  let stx ← chainProofStx n
  return (← solveUsingTactic goal (← `(tactic| exact $stx)), id)

def runBaseline (sizes : List Nat) (showSynth := false) : MetaM Unit := do
  IO.println "=== WordAbs baseline (generated rule-chain term) ==="
  runBench "WordAbs" mkStmt [``chainC] mkExpected solveBaseline (`(tactic| grind)) sizes
    (showSynth := showSynth)

def solveEngine (_n : Nat) (goal : MVarId) : MetaM (List MVarId × (Expr → Expr)) := do
  let (vcs, finalize) ← Ascend.mainWith goal #[]
  return (vcs.toList, finalize)

def runEngine (sizes : List Nat) (showSynth := false) : MetaM Unit := do
  IO.println "=== WordAbs ascend engine ==="
  runBench "WordAbs" mkStmt [``chainC] mkExpected solveEngine
    (`(tactic| first
        | (simp only [ofProp_prop_eq]; assumption)
        | decide
        | (simp only [wordVal, ofProp_prop_eq, UInt64.toNat_add] at *; omega))) sizes
    (showSynth := showSynth)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runBaseline [2] (showSynth := true)

#eval runEngine [2] (showSynth := true)

#eval runBaseline [10, 20, 50, 100, 200, 500, 1000, 2000, 5000]

#eval runEngine [10, 20, 50, 100, 200, 500, 1000, 2000, 5000]
