import Cases.WordAbs
import Driver
open Lean Meta Elab Sym Std.Internal.Do Lean.Order Ascent AscendBench

set_option maxRecDepth 10000

/-- Time `shareCommonInc` per fresh term of a given shape: `mk i` must build a term fresh for
each `i` (a varying literal defeats cross-iteration dedup). -/
def bench (label : String) (nodes : Nat) (reps : Nat) (mk : Nat → Expr) : SymM Unit := do
  -- Warm the table with the constant subterms.
  let _ ← shareCommonInc (mk 0)
  -- Construction alone (defeat dead-code elimination with a cheap observation).
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for i in [1:reps+1] do
    acc := acc + (mk i).approxDepth.toNat
  let t1 ← IO.monoNanosNow
  for i in [1:reps+1] do
    let _ ← shareCommonInc (mk (reps + i))
  let t2 ← IO.monoNanosNow
  let mkPer := (t1 - t0) / reps
  let bothPer := (t2 - t1) / reps
  IO.println s!"{label}: construct {mkPer} ns, construct+share {bothPer} ns, share ≈ {bothPer - min mkPer bothPer} ns ({nodes} fresh nodes, acc {acc % 2})"

#eval show TermElabM _ from do
  -- Representative pieces from the WordAbs goals.
  let rwpApp ← Term.elabTerm (← `(rwp γw (pure 0 : UB Int) (pure 0 : Id UInt64)
    (fun a b => ⌜a = wordVal b⌝) ⊥)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let rwpApp ← instantiateMVars rwpApp
  let lam ← Term.elabTerm (← `(fun (av : Int) (cv : UInt64) =>
    rwp γw (pure av : UB Int) (pure cv : Id UInt64) (fun a b => ⌜a = wordVal b⌝) ⊥)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let lam ← instantiateMVars lam
  let eqE ← Term.elabTerm (← `((0 : Int) = wordVal 7)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let eqE ← instantiateMVars eqE
  let prefix4 := rwpApp.appFn!.appFn!.appFn!.appFn!
  let aSlot := rwpApp.appFn!.appFn!.appFn!.appArg!   -- `pure 0 : UB Int`
  let cSlot := rwpApp.appFn!.appFn!.appArg!
  let qSlot := rwpApp.appFn!.appArg!
  let eSlot := rwpApp.appArg!
  let fresh := fun (e : Expr) (i : Nat) => e.replace fun s =>
    if s.isRawNatLit then some (mkRawNatLit (s.rawNatLit?.getD 0 + 1000 + i)) else none
  SymM.run do
    let _ ← shareCommonInc rwpApp
    let _ ← shareCommonInc lam
    -- 1. Rebuilt goal spine: shared prefix + one fresh volatile slot (the engine's rebuild).
    bench "rwp spine (prefix shared, fresh a)" 8 20000 fun i =>
      mkApp4 prefix4 (fresh aSlot i) cSlot qSlot eSlot
    -- 2. Full 21-node spine rebuild (mkAppN style).
    bench "rwp spine (full mkAppN)" 25 20000 fun i =>
      mkAppN rwpApp.getAppFn ((rwpApp.getAppArgs.set! 17 (fresh aSlot i)))
    -- 3. The rebound coupling lambda, fresh values inside.
    bench "rebound lambda" 30 20000 fun i => fresh lam i
    -- 4. Small coupling prop.
    bench "coupling eq" 6 20000 fun i => fresh eqE i
    -- 5. Already shared: zero fresh nodes, pure invocation overhead.
    let shared ← shareCommonInc rwpApp
    bench "already shared (0 fresh nodes)" 1 20000 fun _ => shared
    -- 6. 100 fresh terms batched into one call.
    bench "batch of 100 eqs (one call)" 600 2000 fun i =>
      mkAppN (mkConst `dummy) ((Array.range 100).map fun j => fresh eqE (i * 100 + j))
