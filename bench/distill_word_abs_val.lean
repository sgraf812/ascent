import Driver
import Cases.WordAbsVal

/-! # Guarded word abstraction through `@[distill_pure]` rules, engine measurements

In the right-nested family the first step adds the two literals `7 + 7`; the value solver works on
the simp normal form `14` of that sum, so the expected program starts with the unguarded value
`wordVal 14`. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBenchVal

def mk (n : Nat) : MetaM DistillBench.Problem := return {
  stmt := ← `(⦃(⊤ : Prop)⦄ (chainC 7 $(quote n)) ⪯[γw] (?_ : Demonic Int) ⦃(⌜FunRel wordVal · ·⌝)⦄)
  expected? := some (← `(chainA 7 $(quote n))) }

def runEngine (sizes : List Nat) (showSynth := false) : MetaM Unit := do
  IO.println "=== WordAbsVal distill engine ==="
  DistillBench.runTactic "WordAbsVal" mk [``chainC] `(tactic| distill)
    `(tactic| simp_all [funRel_iff]) sizes (showSynth := showSynth)

def mkExpectedR : Nat → MetaM Term
  | 0 => `(chainAR 7 (wordVal 7) 0)
  | n + 1 => `(do let r ← (do Demonic.assert True; pure (wordVal 14)); chainAR 7 r $(quote n))

def mkR (n : Nat) : MetaM DistillBench.Problem := return {
  stmt := ← `(⦃(⊤ : Prop)⦄ (chainCR 7 7 $(quote n)) ⪯[γw] (?_ : Demonic Int) ⦃(⌜FunRel wordVal · ·⌝)⦄)
  expected? := some (← mkExpectedR n) }

def runEngineR (sizes : List Nat) (showSynth := false) : MetaM Unit := do
  IO.println "=== WordAbsVal right-nested ==="
  DistillBench.runTactic "WordAbsValR" mkR [``chainCR] `(tactic| distill)
    `(tactic| simp_all [funRel_iff]) sizes (showSynth := showSynth)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runEngine [2] (showSynth := true)

#eval runEngine [120, 240, 360]

#eval runEngineR [120, 240, 360]
