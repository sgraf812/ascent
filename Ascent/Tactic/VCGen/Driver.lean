/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/

import Ascent.Tactic.VCGen.Shim
import Lean.Elab.Tactic.Meta
import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.Solve
import Ascent.Tactic.VCGen.Solve
import Ascent.Tactic.VCGen.PureRefinement
import Lean.Meta.Sym.Grind
import Lean.Elab.Tactic.VCGen.Driver

open Lean Meta Elab Tactic Sym Sym.Internal Lean.Order
open Lean.Elab.Tactic.Do.SpecAttr

namespace Lean.Elab.Tactic.VCGen.Ascend

/-!
Worklist driver for `vcgen`. Wraps `solve` with a queue of pending goals
and emits VCs (or invariant holes) for those `solve` cannot decompose further.
-/


/--
Try to elaborate the user's invariant alt for invariant number `n` inline,
discharging `mv` if successful. Looks up `Context.invariantAlts[n]?` (pre-parsed
in `Frontend`) and dispatches to `exact $rhs` for bullet form or
`rename_i $args*; exact $rhs` for labelled form. Returns whether elaboration
succeeded. Numbering is 1-based; out-of-order labelled forms (e.g. `| inv2 => …`
before `| inv1 => …`) are supported because the map is keyed by parsed number,
not position.
-/
def elabInvariant (invariantAlts : Std.HashMap Nat Syntax) (n : Nat) (mv : MVarId) : SymM Bool := do
  try
    let some alt := invariantAlts[n]? | return false
    let tac ← match alt with
      | `(Lean.Parser.Tactic.invariantDotAlt| · $rhs) => `(tactic| exact $rhs)
      | `(Lean.Parser.Tactic.invariantCaseAlt| | $_tag $args* => $rhs) =>
          `(tactic| (rename_i $args*; exact $rhs))
      | _ => return false
    -- `withDefault`: the surrounding grind context forces reducible transparency,
    -- under which the invariant's type isn't resolved enough for term elaboration
    -- of the alternative's right-hand side to succeed.
    withRef alt <| discard <| Meta.withDefault <| Lean.Elab.runTactic mv tac {} {}
    -- The tactic runs without throwing even when it fails to close the goal;
    -- check explicitly that the MVar got assigned.
    if ← mv.isAssigned then
      -- Preprocess the assignment to `mv` because it will interact with the `SymM` world
      if let some val ← getExprMVarAssignment? mv then
        let val ← unfoldReducible val
        let val ← shareCommon val
        mv.assign val
      return true
    else
      return false
  catch _ => return false

/-- Pull invariant subgoals out of `subgoals` and handle them eagerly: register
each in `State.invariants` (1-based stable index) and try to inline-elaborate
its matching user alt. Returns the remaining non-invariant subgoals for `work`
to enqueue. Eager handling here ensures dependent VCs see `?inv` assigned by
the time they reach `emitVC`. -/
def handleInvariantSubgoals (subgoals : List MVarId) : VCGenM (Array MVarId) := do
  let env ← getEnv
  let mut others : Array MVarId := #[]
  for sg in subgoals do
    if isSpecInvariantType env (← sg.getType) then
      let n := (← get).invariants.size + 1
      modify fun s => { s with invariants := s.invariants.push sg }
      if ← elabInvariant (← read).invariantAlts n sg then
        modify fun s => { s with inlineHandledInvariants := s.inlineHandledInvariants.insert n }
      else
        sg.setKind .syntheticOpaque
    else
      others := others.push sg
  return others

/-- Simplify the target of a verification condition with `Context.simpMethods`. -/
def simpVC (goal : MVarId) : VCGenM Sym.SimpGoalResult := goal.withContext do
  let some methods := (← read).simpMethods | return .noProgress
  let target ← goal.getType
  let (result, simpState') ← Sym.Simp.SimpM.run (Sym.Simp.simp target) methods {} (← get).simpState
  modify fun s => { s with simpState := simpState' }
  result.toSimpGoalResult goal

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
`simp` rewrites the VC only when `reason` says that nothing is left to decompose, so a VC that
`until`, a missing spec or the step limit leaves behind keeps its program as written.
Invariant subgoals are handled separately by `handleInvariantSubgoals` directly inside `work`,
so they never reach this path.
-/
def emitVC (goal : Grind.Goal) (reason : SolveResult.StopReason) : VCGenM Unit := do
  let mut goal := { goal with mvarId := ← elimTopPre goal.mvarId }
  if ← closeByEntry goal.mvarId then return
  if reason matches .noEntailment .. | .noProgress .. then
    -- An invariant from an `invariants` alternative is assigned while the target is built, as in
    -- `?inv pref suff (a, b)`. Instantiating it lets `simp` reduce the body of the invariant.
    let target ← goal.mvarId.getType
    let target' ← instantiateMVarsS target
    unless isSameExpr target target' do
      goal := { goal with mvarId := ← goal.mvarId.replaceTargetDefEqFast target' }
    match ← simpVC goal.mvarId with
    | .closed => return
    | .goal mvarId => goal := { goal with mvarId }
    | .noProgress => pure ()
  goal ← processHypotheses goal
  if goal.inconsistent then return
  let some mvarId ← cleanupVC goal.mvarId | return
  -- The hypotheses `cleanupVC` introduces from the target are rewritten with the simp step.
  let mvarId ← simpHypotheses mvarId
  mvarId.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs.push { goal with mvarId } }

structure WorkItem where
  goal : Grind.Goal
  scope : Scope
  /-- The `@[spec]` scope for the `wp` goals of the worklist. -/
  coreScope : Scope

/-- `true` iff the target of `goal` is `pre ⊑ wp …`, which `vcgen`'s own `solve` decomposes. -/
def isWPGoal (goal : MVarId) : MetaM Bool := do
  let_expr PartialOrder.rel _ _ _ rhs := (← goal.getType).consumeMData | return false
  return (Lean.Elab.Tactic.VCGen.isWPApp? rhs).isSome

def work (scope coreScope : Scope) (goal : Grind.Goal) : VCGenM Unit := do
  let mvarId ← preprocessMVar goal.mvarId
  let mut worklist : Array WorkItem := #[{ goal := { goal with mvarId }, scope, coreScope }]
  let mut holes : Array Grind.Goal := #[]
  while let some s := worklist.back? do
    worklist := worklist.pop
    if ← s.goal.mvarId.isAssigned then continue
    -- A subgoal of data type is a synthesis hole: it stays a natural metavariable until the
    -- worklist is empty, and only then is it emitted, if no step assigned it.
    unless (← Sym.getLevel (← s.goal.mvarId.getType)).isZero do
      holes := holes.push s.goal
      continue
    if let some (jp, jumps) := (← get).pendingJoinPoints[s.goal.mvarId]? then
      modify fun st => { st with pendingJoinPoints := st.pendingJoinPoints.erase s.goal.mvarId }
      finalizeJoinPoint jp jumps
    let goal ← processHypotheses s.goal
    if goal.inconsistent then continue
    if ← isWPGoal goal.mvarId then
      match ← Lean.Elab.Tactic.VCGen.solve s.coreScope goal.mvarId with
      | .stop reason => Lean.Elab.Tactic.VCGen.emitVC goal reason
      | .goals coreScope subgoals =>
        let subgoals ← handleInvariantSubgoals subgoals
        worklist := worklist ++ subgoals.reverse.map (fun mv =>
          { goal := { goal with mvarId := mv }, scope := s.scope, coreScope })
      continue
    match ← solve s.scope goal.mvarId with
    | .stop reason =>
      emitVC goal reason
    | .goals scope subgoals =>
      -- A `PureRefinement` subgoal is solved at once, so that the continuation sees the abstract
      -- value and the precondition.
      let subgoals ← subgoals.filterM fun mv => do
        if ← isPureRefinementGoal mv then solvePureRefinement mv; return false
        return true
      -- Handle invariant subgoals eagerly here, so that VC subgoals popped
      -- from the worklist later see the invariant MVar already assigned.
      -- Non-invariant subgoals go to the worklist as usual and will eventually go through `emitVC`.
      let subgoals ← handleInvariantSubgoals subgoals
      worklist := worklist ++ subgoals.reverse.map (fun mv =>
        { goal := { goal with mvarId := mv }, scope, coreScope := s.coreScope })
  -- A hole is data, not a proposition, so `emitVC` does not simplify it.
  for hole in holes do
    unless ← hole.mvarId.isAssigned do
      emitVC hole .outOfFuel

structure Result where
  /-- All invariant goals emitted during VC generation, in emit order. The MVarId at
  index `i` carries tag `inv{i+1}`, so callers can treat the array index as the
  invariant number. Some entries may already be assigned (inline-elaborated by
  `Driver.emitVC`); the caller is responsible for filtering before discharging. -/
  invariants : Array MVarId
  /-- Unassigned VCs. Each shares the parent `Grind.Goal`'s state. -/
  vcs : Array Grind.Goal
  /-- Invariant numbers handled inline by `Driver.emitVC`. Used by `Frontend` to
  avoid spurious "alt does not match any invariant" warnings for inline-consumed
  alts. -/
  inlineHandledInvariants : Std.HashSet Nat := {}
  /-- Frame terms of `frames` alternatives whose program pattern matched no program. -/
  unmatchedFrames : Array Syntax := #[]

/--
Generate verification conditions for a goal of the form `pre ⊑ wp e post eposts s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.

`stepLimit?`, when `some n`, seeds the fuel counter to `n`; when `none`, fuel is unlimited.
-/
partial def run (goal : Grind.Goal) (ctx : Context) (scope coreScope : Scope)
    (stepLimit? : Option Nat := none) (frameDB : FrameDB := {}) :
    Grind.GrindM Result := do
  let initState : State :=
    { fuel := match stepLimit? with | some n => .limited n | none => .unlimited, frameDB }
  -- VCGen temporarily violates the `SymM` folded-projections invariant: `reduceHead?`
  -- exposes kernel projections in intermediate terms and restores the invariant in its
  -- final result, so the `shareCommon` kernel-projection check is disabled.
  let ((), state) ← Sym.withoutFoldProjsCheck <| StateRefT'.run (ReaderT.run (work scope coreScope goal) ctx) initState
  _ ← state.invariants.mapIdxM fun idx mv => do
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  _ ← state.vcs.mapIdxM fun idx g => do
    g.mvarId.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← g.mvarId.getTag).eraseMacroScopes)
  let vcs ← state.vcs.filterM (not <$> ·.mvarId.isAssigned)
  let unmatchedFrames := state.frameDB.entries.filterMap fun e =>
    if e.retired then none else some e.frameStx
  return {
    invariants := state.invariants,
    vcs,
    inlineHandledInvariants := state.inlineHandledInvariants,
    unmatchedFrames }


end Lean.Elab.Tactic.VCGen.Ascend
