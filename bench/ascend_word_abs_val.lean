import Driver
import Cases.WordAbsVal

/-! # Guarded word abstraction through `@[ascend_pure]` rules, engine measurements

In the right-nested family the first step adds the two literals `7 + 7`; the value solver works on
the simp normal form `14` of that sum, so the expected program starts with the unguarded value
`wordVal 14`. -/

open Lean Meta Elab Std.WP Lean.Order Ascent AscendBenchVal

def mkStmt (n : Nat) : MetaM Term :=
  `(⦃(⊤ : Prop)⦄ (chainC 7 $(quote n)) ⪯[γw] (?_ : UB Int) ⦃(⌜FunRel wordVal · ·⌝)⦄)

def mkExpected (n : Nat) : MetaM Term :=
  `(chainA 7 $(quote n))

def solveEngine (_n : Nat) (goal : MVarId) : MetaM (List MVarId) := do
  AscendBench.solveUsingTactic goal (← `(tactic| ascend))

def runEngine (sizes : List Nat) (showSynth := false) : MetaM Unit := do
  IO.println "=== WordAbsVal ascend engine ==="
  AscendBench.runBench "WordAbsVal" mkStmt [``chainC] mkExpected solveEngine
    (`(tactic| simp_all [funRel_iff])) sizes (showSynth := showSynth)

def mkStmtR (n : Nat) : MetaM Term :=
  `(⦃(⊤ : Prop)⦄ (chainCR 7 7 $(quote n)) ⪯[γw] (?_ : UB Int) ⦃(⌜FunRel wordVal · ·⌝)⦄)

def mkExpectedR : Nat → MetaM Term
  | 0 => `(chainAR 7 (wordVal 7) 0)
  | n + 1 => `(do let r ← (do UB.assume True; pure (wordVal 14)); chainAR 7 r $(quote n))

def runEngineR (sizes : List Nat) (showSynth := false) : MetaM Unit := do
  IO.println "=== WordAbsVal right-nested ==="
  AscendBench.runBench "WordAbsValR" mkStmtR [``chainCR] mkExpectedR solveEngine
    (`(tactic| simp_all [funRel_iff])) sizes (showSynth := showSynth)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runEngine [2] (showSynth := true)

#eval runEngine [10, 20, 50, 100, 200, 500, 1000, 2000, 5000]

#eval runEngineR [10, 20, 50, 100, 200, 500, 1000, 2000, 5000]
