import Lean
import Ascent.Corres.RTriple

/-!
# The ascend benchmark driver

Runs one synthesis problem per size: elaborate an `RTriple` statement with a `?a` hole for the
abstract program, unseal the hole to a natural metavariable, unfold the concrete program's
definitions via `Sym.simp`, hand the goal to a solver, and measure each phase separately: solve
time, VC count and discharge time, the golden `isDefEq` check of the synthesized program against
its expected image, and kernel-checking time of the final proof (after `shareCommon`).
-/

open Lean Meta Elab Sym

namespace AscendBench

def timeItMs {α : Type} (k : MetaM α) : MetaM (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← k
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0) / 1000000)

/-- Elaborate a synthesis statement: an `RTriple` proposition with a single `?a` hole for the
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

/--
Run one synthesis benchmark and print a measurement line.

* `stmt`: the `RTriple` statement with its `?a` hole.
* `unfold`: definitions to unfold in the goal via `Sym.simp` (the concrete program's equations);
  unfolding is not measured.
* `expected`: the expected abstract program, for the golden `isDefEq` check.
* `solve`: the solver under measurement; returns residual VCs.
* `discharge`: tactic for the residual VCs (forced only when there are any).
-/
def driver (label : String) (stmt : Term) (unfold : List Name) (expected : Term)
    (solve : MVarId → MetaM (List MVarId)) (discharge : MetaM (TSyntax `tactic))
    (showSynth : Bool := false) : TermElabM Unit := do
  let (ty, aMVar) ← elabSynthGoal stmt
  let expectedE ← Term.elabTermEnsuringType expected (← inferType (mkMVar aMVar))
  Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← mkFreshExprSyntheticOpaqueMVar ty
  let (goal, _unfoldMs) ← timeItMs <| SymM.run do
    let goal ← preprocessMVar proof.mvarId!
    let eqnss ← unfold.toArray.mapM fun n => getEqnsFor? n
    let thms := eqnss.flatMap (·.getD #[])
    match ← Sym.simpGoal goal (← Sym.mkMethods thms) with
    | .goal goal => return goal
    | .noProgress => throwError "no progress unfolding {unfold} in {goal}"
    | .closed => throwError "unfolding closed the goal"
  let (vcs, solveMs) ← timeItMs (solve goal)
  let dischargeMs? ← OptionT.run do
    guard !vcs.isEmpty
    let tac ← discharge
    Prod.snd <$> timeItMs do
      for vc in vcs do
        let [] ← solveUsingTactic vc tac
          | throwError "discharge failed on {vc}"
  if showSynth then
    logInfo m!"{label} synthesized:{indentExpr (← instantiateMVars (mkMVar aMVar))}"
  let (goldenOk, goldenMs) ← timeItMs do
    isDefEq (← instantiateMVars (mkMVar aMVar)) expectedE
  let (prf, instMs) ← timeItMs (instantiateMVars proof)
  let prf := ShareCommon.shareCommon prf
  let (_, kernelMs) ← timeItMs (checkWithKernel prf)
  let pad := "".pushn ' ' (20 - min label.length 20)
  let mut msg := s!"{label}:{pad}solve {solveMs} ms"
  if let some dischargeMs := dischargeMs? then
    msg := msg ++ s!", {vcs.length} VCs: {dischargeMs} ms"
  else
    msg := msg ++ s!", {vcs.length} VCs"
  msg := msg ++ s!", golden{if goldenOk then "" else " FAILED"} {goldenMs} ms"
  if instMs > 1000 then
    msg := msg ++ s!", instantiate {instMs} ms"
  msg := msg ++ s!", kernel {kernelMs} ms"
  IO.println msg

/-- Run a benchmark family over `sizes`. `mkStmt`/`mkExpected` build the per-size statement and
expected program; `solve` gets the size for solvers that generate size-dependent proofs. -/
def runBench (label : String) (mkStmt : Nat → MetaM Term) (unfold : List Name)
    (mkExpected : Nat → MetaM Term) (solve : Nat → MVarId → MetaM (List MVarId))
    (discharge : MetaM (TSyntax `tactic)) (sizes : List Nat) (showSynth : Bool := false) :
    MetaM Unit := do
  for n in sizes do
    Term.TermElabM.run' do
      driver s!"{label}({n})" (← mkStmt n) unfold (← mkExpected n) (solve n) discharge
        (showSynth := showSynth)

end AscendBench
