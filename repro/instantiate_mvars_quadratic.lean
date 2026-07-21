import Lean
open Lean Meta

/-!
# Faithful MWE: Θ(n²) `instantiateMVars` on a Θ(n) maximally-shared proof DAG.

Mechanism (`src/library/instantiate_mvars.cpp`, `instantiate_delayed_fn`): pass 2's
cache is keyed on `(expr.raw(), m_depth)` — the *binder depth*. A shared subterm that
must be visited at many different depths is a cache miss at each depth and gets
re-traversed, even when the traversal changes nothing and returns the same pointer.

Construction. A fixed outer free variable `c : Nat` sits in the local context before
any intro. A shared accumulator threads through it:

    s₀ = 1 + c,   sₖ = 1 + sₖ₋₁         (each sₖ literally shares the node sₖ₋₁)

Every `sₖ` is bvar-free (built only from `c` and the literal `1`), so it is
pointer-shared across all depths of the *closed* proof term ⇒ Θ(n) DAG after
hash-consing. We build the telescope

    ∀ (h₀ : D₀) … (h_{n-1} : D_{n-1}), sₙ = sₙ

and prove it by `intro`-ing all `n` binders one at a time (an `n`-long delayed chain),
then assigning `Eq.refl sₙ`. The finalized proof `fun h₀ … h_{n-1} => Eq.refl sₙ`
carries the shared chain in its binder domains AND its leaf.

  dep = true   (FAITHFUL, quadratic):  Dₖ := (sₖ = sₖ)   -- shared chain at EVERY depth
  dep = false  (CONTROL,  linear):     Dₖ := (0 = 0)     -- chain only in the leaf (one depth)

Both are Θ(n)-size. The sole difference is whether the shared chain appears in the
binder domains (visited at n growing depths ⇒ n² cache-missing re-traversals) or only
in the leaf (one depth ⇒ linear). `c` free ⇒ pass 2 never early-exits on `sₖ`, so the
re-traversal actually runs; every node is unchanged, so update_* returns the original
pointer ⇒ Θ(n) output. Θ(n²) time on Θ(n) output: the faithful pathology.
-/

-- Distinct structural subterms = minimal maximally-shared DAG node count.
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

structure Sample where
  delayed : Nat
  dag     : Nat
  us      : Nat

/-- With `c : Nat` fixed in the context, build the telescope over the shared `c`-chain,
    intro all `n` binders one at a time (an `n`-long delayed chain), assign `Eq.refl sₙ`,
    time ONLY `instantiateMVars`, and measure the resulting (open, `c`-carrying) DAG. -/
def run (n : Nat) (dep : Bool) (verify : Bool := false) : MetaM Sample :=
  withLocalDeclD `c (mkConst ``Nat) fun c => do
    -- Shared accumulator: reuse the SAME `sₖ₋₁` object inside `sₖ` (real pointer sharing).
    let one := mkNatLit 1
    let mut s := mkApp2 (mkConst ``Nat.add) one c        -- s₀ = 1 + c
    let mut domains : Array Expr := #[]
    for _ in [0:n] do
      let d ← if dep then mkEq s s else mkEq (mkNatLit 0) (mkNatLit 0)
      domains := domains.push d
      s := mkApp2 (mkConst ``Nat.add) one s              -- sₖ = 1 + sₖ₋₁
    let sn := s                                          -- sₙ references every level via the chain
    -- ∀ (h₀ : D₀) … (h_{n-1} : D_{n-1}), sₙ = sₙ    (domains are Props ⇒ non-dependent binders)
    let type ← domains.foldrM (fun d acc => mkArrow d acc) (← mkEq sn sn)
    let mv ← mkFreshExprSyntheticOpaqueMVar type
    let mut g := mv.mvarId!
    for _ in [0:n] do
      let (_, g') ← g.intro1
      g := g'
    g.assign (← g.withContext (mkEqRefl sn))
    let delayed := (← getMCtx).dAssignment.toList.length
    let t0 ← IO.monoNanosNow
    let prf ← instantiateMVars (mkMVar mv.mvarId!)       -- the ONLY timed call
    let us := ((← IO.monoNanosNow) - t0) / 1000
    if verify then
      Meta.check prf
      IO.println s!"Meta.check FAITHFUL n={n}: OK  (isTypeCorrect = {← isTypeCorrect prf})\n"
    return { delayed, dag := dagSize prf, us }

def fmtRatio (cur : Nat) (prev : Option Nat) : String :=
  match prev with
  | some p => if p == 0 then "n/a" else s!"{(Float.ofNat cur / Float.ofNat p)}"
  | none   => "-"

set_option maxRecDepth 1000000 in
#eval show MetaM Unit from do
  let ns := [100, 200, 400, 800, 1600]
  let mctx0 ← getMCtx
  let _ ← run 200 true (verify := true)
  setMCtx mctx0
  for (label, dep) in [("FAITHFUL (dep domains: shared chain at every depth)", true),
                       ("CONTROL  (const domains: chain only in leaf)",        false)] do
    IO.println s!"--- {label} ---"
    IO.println "     N   delayed        DAG   DAGx   instUs   instX"
    let mut pDag : Option Nat := none
    let mut pMs  : Option Nat := none
    for n in ns do
      let mctx ← getMCtx
      let s ← run n dep
      setMCtx mctx
      IO.println s!"{n}   {s.delayed}   {s.dag}   {fmtRatio s.dag pDag}   {s.us}  {fmtRatio s.us pMs}"
      pDag := some s.dag; pMs := some s.us
    IO.println ""
