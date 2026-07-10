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

/-- The same fresh-term stream through a locally held factory state: `transient? = true`
uses the destructive `objectFactory` (exclusive state, in-place updates), `false` the
`persistentObjectFactory` Sym uses (snapshot-friendly, functional updates). -/
def benchFactory (label : String) (nodes reps : Nat) (transient? : Bool) (mk : Nat → Expr) :
    IO Unit := do
  if transient? then
    let mut st : ShareCommon.State ShareCommon.objectFactory := .mk _
    (st, _) := Prod.swap (st.shareCommon (mk 0))
    let t0 ← IO.monoNanosNow
    for i in [1:reps+1] do
      let (_, st') := st.shareCommon (mk i)
      st := st'
    let t1 ← IO.monoNanosNow
    IO.println s!"{label}: {(t1-t0)/reps} ns/term, ~{(t1-t0)/reps/nodes} ns/node"
  else
    let mut st : ShareCommon.State ShareCommon.persistentObjectFactory := .mk _
    (st, _) := Prod.swap (st.shareCommon (mk 0))
    let t0 ← IO.monoNanosNow
    for i in [1:reps+1] do
      let (_, st') := st.shareCommon (mk i)
      st := st'
    let t1 ← IO.monoNanosNow
    IO.println s!"{label}: {(t1-t0)/reps} ns/term, ~{(t1-t0)/reps/nodes} ns/node"

/-! A hand-rolled transient interner: pointer memo + structural table over `Std.HashMap`,
held exclusively so in-place updates fire. Children are canonicalized first, so structural
comparison is pointer comparison; binder names are ignored (alpha). -/

structure TSt where
  memo  : Std.HashMap USize Expr := {}
  table : Std.HashMap UInt64 (List Expr) := {}

unsafe def tkey (e : Expr) : UInt64 :=
  match e with
  | .app f a => mixHash 11 (mixHash (ptrAddrUnsafe f).toUInt64 (ptrAddrUnsafe a).toUInt64)
  | .lam _ t b i =>
    mixHash 13 (mixHash (ptrAddrUnsafe t).toUInt64
      (mixHash (ptrAddrUnsafe b).toUInt64 (hash i.toUInt64)))
  | .forallE _ t b i =>
    mixHash 17 (mixHash (ptrAddrUnsafe t).toUInt64
      (mixHash (ptrAddrUnsafe b).toUInt64 (hash i.toUInt64)))
  | e => e.hash

unsafe def teqv (a b : Expr) : Bool :=
  match a, b with
  | .app f1 a1, .app f2 a2 => ptrAddrUnsafe f1 == ptrAddrUnsafe f2 && ptrAddrUnsafe a1 == ptrAddrUnsafe a2
  | .lam _ t1 b1 i1, .lam _ t2 b2 i2 =>
    ptrAddrUnsafe t1 == ptrAddrUnsafe t2 && ptrAddrUnsafe b1 == ptrAddrUnsafe b2 && i1 == i2
  | .forallE _ t1 b1 i1, .forallE _ t2 b2 i2 =>
    ptrAddrUnsafe t1 == ptrAddrUnsafe t2 && ptrAddrUnsafe b1 == ptrAddrUnsafe b2 && i1 == i2
  | .const n1 l1, .const n2 l2 => n1 == n2 && l1 == l2
  | .lit l1, .lit l2 => l1 == l2
  | .sort u1, .sort u2 => u1 == u2
  | .fvar i1, .fvar i2 => i1 == i2
  | .mvar i1, .mvar i2 => i1 == i2
  | .bvar i1, .bvar i2 => i1 == i2
  | _, _ => false

unsafe def tshare (e : Expr) : StateM TSt Expr := do
  if let some c := (← get).memo[ptrAddrUnsafe e]? then return c
  let e' ← match e with
    | .app f a => do
      let f' ← tshare f; let a' ← tshare a
      pure <| if ptrAddrUnsafe f' == ptrAddrUnsafe f && ptrAddrUnsafe a' == ptrAddrUnsafe a
              then e else .app f' a'
    | .lam n t b i => do
      let t' ← tshare t; let b' ← tshare b
      pure <| if ptrAddrUnsafe t' == ptrAddrUnsafe t && ptrAddrUnsafe b' == ptrAddrUnsafe b
              then e else .lam n t' b' i
    | .forallE n t b i => do
      let t' ← tshare t; let b' ← tshare b
      pure <| if ptrAddrUnsafe t' == ptrAddrUnsafe t && ptrAddrUnsafe b' == ptrAddrUnsafe b
              then e else .forallE n t' b' i
    | .mdata m b => do pure <| .mdata m (← tshare b)
    | .proj s i b => do pure <| .proj s i (← tshare b)
    | e => pure e
  let k := tkey e'
  let cands := (← get).table.getD k []
  for c in cands do
    if teqv c e' then
      modify fun st => { st with memo := st.memo.insert (ptrAddrUnsafe e) c }
      return c
  modify fun st =>
    { memo := st.memo.insert (ptrAddrUnsafe e) e'
      table := st.table.insert k (e' :: cands) }
  return e'

unsafe def benchT (label : String) (nodes reps : Nat) (mk : Nat → Expr) : IO Unit := do
  let mut st : TSt := {}
  let (_, st0) := (tshare (mk 0)).run {}
  st := st0
  let t0 ← IO.monoNanosNow
  for i in [1:reps+1] do
    let (_, st') := (tshare (mk i)).run st
    st := st'
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1-t0)/reps} ns/term, ~{(t1-t0)/reps/nodes} ns/node"

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
    -- 7/8. The factory experiment: same stream, transient vs persistent factory, locally
    -- held state (never stored in a ref, so it stays exclusive).
    unsafe benchT "transient interner: eq" 6 20000 fun i => fresh eqE i
    unsafe benchT "transient interner: lambda" 30 20000 fun i => fresh lam i
    unsafe benchT "transient interner: batch100" 600 2000 fun i =>
      mkAppN (mkConst `dummy) ((Array.range 100).map fun j => fresh eqE (i * 100 + j))
