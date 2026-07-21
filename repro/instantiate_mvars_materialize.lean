import Lean
open Lean Meta

/-!
# Probe: single-pass sharing-preserving materialization vs the delayed collapse.

Same faithful telescope as `faithful_mwe.lean` (shared `c`-chain in every binder domain).
Two ways to produce the SAME closed proof `fun h₀ … h_{n-1} => Eq.refl sₙ`:

  INTRO  : intro all n binders one at a time (n-long delayed chain), then instantiateMVars.
           This is what the engine does. Θ(n²) (depth-keyed cache re-traversal).
  DIRECT : forallTelescope + a SINGLE `mkLambdaFVars` over the fvar-form leaf — one
           abstraction pass, sharing preserved, no delayed chain. Θ(n).

Both yield the identical hash-consed DAG; only the materialization cost differs.
-/

partial def collect (e : Expr) : StateM (Std.HashSet Expr) Unit := do
  if (← get).contains e then return
  modify (·.insert e)
  match e with
  | .app f a => collect f; collect a
  | .lam _ d b _ | .forallE _ d b _ => collect d; collect b
  | .letE _ t v b _ => collect t; collect v; collect b
  | .mdata _ b | .proj _ _ b => collect b
  | _ => pure ()
def dagSize (e : Expr) : Nat := ((collect e).run {}).2.size

def mkType (n : Nat) (c : Expr) : MetaM (Expr × Expr) := do
  let one := mkNatLit 1
  let mut s := mkApp2 (mkConst ``Nat.add) one c
  let mut domains : Array Expr := #[]
  for _ in [0:n] do
    domains := domains.push (← mkEq s s)
    s := mkApp2 (mkConst ``Nat.add) one s
  return (← domains.foldrM (fun d acc => mkArrow d acc) (← mkEq s s), s)

def runIntro (n : Nat) : MetaM (Nat × Nat) :=
  withLocalDeclD `c (mkConst ``Nat) fun c => do
    let (type, sn) ← mkType n c
    let mv ← mkFreshExprSyntheticOpaqueMVar type
    let mut g := mv.mvarId!
    for _ in [0:n] do let (_, g') ← g.intro1; g := g'
    g.assign (← g.withContext (mkEqRefl sn))
    let t0 ← IO.monoNanosNow
    let prf ← instantiateMVars (mkMVar mv.mvarId!)
    return (((← IO.monoNanosNow) - t0) / 1000, dagSize prf)

/-- Single materialization pass: build the leaf in the fully-extended context, then
    abstract all binders in ONE `mkLambdaFVars`. No metavariables, no delayed chain. -/
def runDirect (n : Nat) : MetaM (Nat × Nat) :=
  withLocalDeclD `c (mkConst ``Nat) fun c => do
    let (type, sn) ← mkType n c
    let t0 ← IO.monoNanosNow
    let prf ← forallTelescope type fun xs _ => do mkLambdaFVars xs (← mkEqRefl sn)
    let us := ((← IO.monoNanosNow) - t0) / 1000
    return (us, dagSize prf)

def fmt (cur : Nat) (prev : Option Nat) : String :=
  match prev with | some p => if p==0 then "n/a" else s!"{Float.ofNat cur/Float.ofNat p}" | none => "-"

set_option maxRecDepth 1000000 in
#eval show MetaM Unit from do
  let ns := [200, 400, 800]
  for (label, run) in [("INTRO  (delayed collapse)", runIntro), ("DIRECT (single mkLambdaFVars pass)", runDirect)] do
    IO.println s!"--- {label} ---"
    IO.println "     N   materializeUs   Us x   DAG"
    let mut pUs : Option Nat := none
    for n in ns do
      let mctx ← getMCtx
      let (us, dag) ← run n
      setMCtx mctx
      IO.println s!"{n}   {us}   {fmt us pUs}   {dag}"
      pUs := some us
    IO.println ""
