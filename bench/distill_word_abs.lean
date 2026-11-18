import Driver
import Cases.WordAbs

/-!
# Guarded word abstraction, baseline measurements

The baseline solver builds the rule-chain proof directly as a term (one `bindChain` per
concrete bind, `refines_addW` at each leaf, `Refinement.pure_eq` at the seed) and elaborates it
once with `exact`. It performs no search and no rule-database lookup, so it is the
speed-of-light reference for the distill engine on this family: measured cost is elaboration,
unification, and kernel checking of the synthesized proof.
-/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench

/-- The rule-chain proof for `chainC 7 n`, as a term. -/
partial def chainProofStx : Nat → MetaM Term
  | 0 => `(Refinement.pure_eq (f := wordVal) ⊤ _ rfl)
  | n+1 => do `(bindChain $(← chainProofStx n) fun cv av => refines_addW av cv _)

def mk (n : Nat) : MetaM DistillBench.Problem := return {
  stmt := ← `(⦃(⊤ : Prop)⦄ (chainC 7 $(quote n)) ⪯[γw] (?_ : Demonic Int) ⦃(⌜wordVal · = ·⌝)⦄)
  expected? := some (← `(chainA 7 $(quote n))) }

def solveBaseline (n : Nat) (goal : MVarId) : MetaM (List MVarId) := do
  let stx ← chainProofStx n
  solveUsingTactic goal (← `(tactic| exact $stx))

def runBaseline (sizes : List Nat) (showSynth := false) : MetaM Unit := do
  IO.println "=== WordAbs baseline (generated rule-chain term) ==="
  runFamily "WordAbs" mk [``chainC] solveBaseline (`(tactic| grind)) sizes (showSynth := showSynth)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runBaseline [2] (showSynth := true)

#eval runBaseline [120, 240, 360]

