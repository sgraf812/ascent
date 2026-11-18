import Lean
import Distillery.Refinement
import Distillery.Tactic.VCGen.Command

/-!
# The distill benchmark driver

The driver runs one synthesis problem per size. It elaborates a `Refinement` statement with a `?a`
hole for the abstract program, under the binders of the problem, and unseals the hole to a natural
metavariable. It unfolds the definitions of the concrete program by `Sym.simp`, hands the goal to a
solver, and measures each phase separately: the solve time, the number of verification conditions
and the time of the tactic that closes them, the golden `isDefEq` check of the synthesized program
against its expected image, the `sym_simp_def` simplification of the synthesized program, and the
kernel check of the final proof after `shareCommon`. The last field is the wall time of all phases.
-/

open Lean Meta Elab Sym

namespace DistillBench

def timeItMs {α : Type} (k : MetaM α) : MetaM (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← k
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0) / 1000000)

/-- Elaborate a synthesis statement: a `Refinement` proposition with a single `?a` hole for the
abstract program. Returns the goal type and the hole, unsealed to a natural metavariable so that
rule application can instantiate it. -/
def elabSynthGoal (stmt : Term) : TermElabM (Expr × MVarId) := do
  let ty ← Term.elabTerm stmt (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let mvars ← getMVars ty
  let #[aMVar] := mvars
    | throwError "expected exactly one hole in the synthesis statement, found {mvars.size}"
  aMVar.setKind .natural
  return (ty, aMVar)

/-- Run the tactic `tac` on `goal`, returning the remaining goals. -/
def solveUsingTactic (goal : MVarId) (tac : TSyntax `tactic) : MetaM (List MVarId) := do
  let (mvarIds, _) ← Lean.Elab.runTactic goal tac.raw {} {}
  return mvarIds

/-- The simplification of `sym_simp_def a from c using pre [ps] post [qs]`, applied to `c`:
`Sym.simp` with the rewrite rules `ps` before and the rules `qs` and the `vcgen_simp` set after
visiting the subterms of a term. -/
def symSimpDef (c : Expr) (pre post : List Name) : MetaM Expr := do
  let mkThms (ns : List Name) : MetaM Sym.Simp.Theorems := do
    let mut thms : Sym.Simp.Theorems := {}
    for n in ns do
      for thm in ← Sym.Simp.mkTheoremsFromDecl n do
        thms := thms.insert thm
    return thms
  let preThms ← mkThms pre
  let postThms ← mkThms post
  let vcThms ← Lean.Elab.Tactic.VCGen.vcgenSimpExt.getTheorems
  let params ← Grind.mkDefaultParams {}
  let discharge := Lean.Elab.Tactic.VCGen.Distill.dischargeSimpSelfOrGrind params
  Sym.SymM.run do
    let c ← Sym.shareCommon c
    let methods : Sym.Simp.Methods :=
      { pre := Sym.Simp.beta >> Sym.Simp.reduceProj >> Sym.Simp.reduceMatcher >>
          Sym.Simp.reduceControl >> preThms.rewrite discharge
        post := Sym.Simp.evalGround >> Grind.NormSym.reduceCtorEq >> vcThms.rewrite >>
          postThms.rewrite discharge }
    let (r, _) ← Sym.Simp.SimpM.run (Sym.Simp.simp c) methods { maxDischargeDepth := 64 }
    match r with
    | .rfl .. => return c
    | .step e .. => instantiateMVars e

@[noinline] def shareCommonAt (e : Expr) (_ : Nat) : Expr := ShareCommon.shareCommon e

/-- One synthesis problem of a family. -/
structure Problem where
  /-- The binders of the statement, such as the parameters of the concrete program. -/
  binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  /-- The `Refinement` statement with its `?a` hole. -/
  stmt : Term
  /-- The expected abstract program, for the golden `isDefEq` check. -/
  expected? : Option Term := none

/--
Run one synthesis benchmark and print a measurement line.

* `unfold`: definitions to unfold in the goal by `Sym.simp`, the equations of the concrete program.
* `solve`: the solver under measurement, which returns the verification conditions.
* `discharge`: the tactic for the verification conditions, run only when there are any.
* `symSimp?`: the rules `(pre, post)` of a `sym_simp_def` step on the synthesized program.
-/
def driver (label : String) (prob : Problem) (unfold : List Name)
    (solve : MVarId → MetaM (List MVarId)) (discharge : MetaM (TSyntax `tactic))
    (symSimp? : Option (List Name × List Name) := none) (showSynth : Bool := false) :
    TermElabM Unit := do
  let t0 ← IO.monoNanosNow
  Term.elabBinders prob.binders fun xs => do
  let (ty, aMVar) ← elabSynthGoal prob.stmt
  let aTy ← inferType (mkMVar aMVar)
  let expectedE? ← prob.expected?.mapM fun e => Term.elabTermEnsuringType e aTy
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← mkFreshExprSyntheticOpaqueMVar ty
  let (goal, unfoldMs) ← timeItMs <| SymM.run do
    let goal ← preprocessMVar proof.mvarId!
    if unfold.isEmpty then return goal
    let eqnss ← unfold.toArray.mapM fun n => getEqnsFor? n
    let thms := eqnss.flatMap (·.getD #[])
    match ← Sym.simpGoal goal (← Sym.mkMethods thms) with
    | .goal goal => return goal
    | .noProgress => throwError "no progress unfolding {unfold} in {goal}"
    | .closed => throwError "unfolding closed the goal"
  let (vcs, solveMs) ← timeItMs (solve goal)
  let dischargeMs ← if vcs.isEmpty then pure 0 else do
    let tac ← discharge
    Prod.snd <$> timeItMs do
      for vc in vcs do
        let [] ← solveUsingTactic vc tac
          | throwError "discharge failed on {vc}"
  let (a, instAMs) ← timeItMs (instantiateMVars (mkMVar aMVar))
  if showSynth then
    logInfo m!"{label} synthesized:{indentExpr a}"
  let golden? ← expectedE?.mapM fun expectedE => timeItMs (isDefEq a expectedE)
  let simpMs? ← symSimp?.mapM fun (pre, post) => do
    let (b, simpMs) ← timeItMs (symSimpDef a pre post)
    if showSynth then
      logInfo m!"{label} simplified:{indentExpr b}"
    return simpMs
  let (prf, instPMs) ← timeItMs do instantiateMVars (← mkLambdaFVars xs proof)
  let instMs := instAMs + instPMs
  -- `shareCommon` is pure: its argument `s0` and the test on its result keep it between the two
  -- clock reads.
  let s0 ← IO.monoNanosNow
  let prf := shareCommonAt prf s0
  let s1 ← if prf.approxDepth == 0 then pure s0 else IO.monoNanosNow
  let shareMs := (s1 - s0) / 1000000
  let (_, kernelMs) ← timeItMs (checkWithKernel prf)
  let t1 ← IO.monoNanosNow
  let pad := "".pushn ' ' (22 - min label.length 22)
  let mut msg := s!"{label}:{pad}unfold {unfoldMs} ms, solve {solveMs} ms, {vcs.length} VCs, \
    finish {dischargeMs} ms"
  if let some (ok, goldenMs) := golden? then
    msg := msg ++ s!", golden{if ok then "" else " FAILED"} {goldenMs} ms"
  if let some simpMs := simpMs? then
    msg := msg ++ s!", sym_simp_def {simpMs} ms"
  msg := msg ++ s!", instantiate {instMs} ms, share {shareMs} ms, kernel {kernelMs} ms, \
    total {(t1 - t0) / 1000000} ms"
  IO.println msg

/-- Run a benchmark family over `sizes`. `mk` builds the problem of each size, and `solve` gets the
size for solvers that generate size-dependent proofs. -/
def runFamily (label : String) (mk : Nat → MetaM Problem) (unfold : List Name)
    (solve : Nat → MVarId → MetaM (List MVarId)) (discharge : MetaM (TSyntax `tactic))
    (sizes : List Nat) (symSimp? : Option (List Name × List Name) := none)
    (showSynth : Bool := false) : MetaM Unit := do
  for n in sizes do
    -- A fresh `Meta` state per size: sharing the metavariable context and caches across
    -- sizes lets earlier runs pollute later measurements.
    (Term.TermElabM.run' do
      driver s!"{label}({n})" (← mk n) unfold (solve n) discharge (symSimp? := symSimp?)
        (showSynth := showSynth) : MetaM Unit).run' {} {}

/-- `runFamily` for a solver that runs the tactic `tac`. -/
def runTactic (label : String) (mk : Nat → MetaM Problem) (unfold : List Name)
    (tac : MetaM (TSyntax `tactic)) (discharge : MetaM (TSyntax `tactic)) (sizes : List Nat)
    (symSimp? : Option (List Name × List Name) := none) (showSynth : Bool := false) :
    MetaM Unit :=
  runFamily label mk unfold (fun _ goal => do solveUsingTactic goal (← tac)) discharge sizes
    (symSimp? := symSimp?) (showSynth := showSynth)

end DistillBench
