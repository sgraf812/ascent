import Driver
import Cases.WordAbsVal

/-! # Guarded word abstraction through `@[ascend_pure]` rules, engine measurements -/

open Lean Meta Elab Std.WP Lean.Order Ascent AscendBenchVal

def mkStmt (n : Nat) : MetaM Term :=
  `(⦃(⊤ : Prop)⦄ (chainC 7 $(quote n)) ⪯[γw] (?_ : UB Int) ⦃(⌜FunRel wordVal · ·⌝)⦄)

def mkExpected (n : Nat) : MetaM Term :=
  `(chainA 7 $(quote n))

def solveEngine (_n : Nat) (goal : MVarId) : MetaM (List MVarId) := do
  AscendBench.solveUsingTactic goal (← `(tactic| ascend'))

def runEngine (sizes : List Nat) (showSynth := false) : MetaM Unit := do
  IO.println "=== WordAbsVal ascend engine ==="
  AscendBench.runBench "WordAbsVal" mkStmt [``chainC] mkExpected solveEngine
    (`(tactic| simp_all [funRel_iff])) sizes (showSynth := showSynth)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runEngine [2] (showSynth := true)

#eval runEngine [10, 20, 50, 100, 200, 500, 1000, 2000, 5000]
