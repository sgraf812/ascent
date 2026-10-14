import Lean
import Ascent.Corres.Refinement

/-!
# The `@[ascend]` spec registry

Registered specs are `Refinement` theorems in registry form: the coupling `Q` (and the exception
coupling `E`, when present) is a universally quantified variable, so the spec applies to any
coupling by assignment, and the synthesis directives live in the abstract program and the
precondition. Specs are keyed in a discrimination tree by their concrete program.

Registration records the telescope positions the engine instantiates at application time:

* `qPosition`/`ePosition?`: the coupling slots, assigned the goal's couplings (auto-framing).
* `avPositions`: the abstract-input variables, those occurring in the abstract program but not
  in the concrete one. At application the goal's abstract slot is `?m t₁ … tₖ`; the engine pins
  the k abstract inputs to the `tᵢ` and assigns `?m` the spec's abstract program with the
  inputs abstracted.
-/

open Lean Meta

namespace Ascend

/-- A registered `@[ascend]` spec. -/
structure SpecInfo where
  declName : Name
  /-- Telescope positions of the abstract-input variables, in binder order. -/
  avPositions : Array Nat
  /-- Telescope position of the coupling variable `Q`. -/
  qPosition : Nat
  /-- Telescope position of the exception coupling `E`, when it is a variable. -/
  ePosition? : Option Nat
  /-- Discrimination-key count, a specificity proxy: candidates are tried most specific
  first, so a `pure (_ + _)` spec beats a bare `pure _` spec on an addition. -/
  specificity : Nat
  deriving Inhabited, BEq

/-- The positions of the metavariables of `e` in the telescope `xs`. -/
private def mvarPositions (xs : Array Expr) (e : Expr) : MetaM (Array Nat) := do
  let mut acc := #[]
  let mvars ← getMVars e
  for h : i in [:xs.size] do
    if mvars.contains xs[i].mvarId! then
      acc := acc.push i
  return acc

/-- Analyze a spec theorem: locate the `Refinement` conclusion, classify the telescope binders,
and compute the discrimination keys of the concrete program. The telescope is instantiated
with metavariables so the keys index binders as wildcards, and non-reducing because at the
`Prop` lattice `Refinement` would reduce to an implication whose precondition the telescope would
consume as a binder. -/
def analyzeSpec (declName : Name) : MetaM (SpecInfo × Array (DiscrTree.Key)) := do
  let info ← getConstInfo declName
  let (xs, _, body) ← forallMetaTelescope info.type
  do
    unless body.isAppOfArity ``Ascent.Refinement 22 do
      throwError "@[ascend]: conclusion of {declName} is not an Refinement application:{indentExpr body}"
    let args := body.getAppArgs
    let a := args[13]!
    let c := args[14]!
    let Q := args[20]!
    let E := args[21]!
    let some qPosition := xs.idxOf? Q
      | throwError "@[ascend]: the coupling of {declName} is not a variable; registry specs \
          must be Q-generalized:{indentExpr Q}"
    let ePosition? := xs.idxOf? E
    let cPositions ← mvarPositions xs c
    -- Synthesis holes are the value inputs and the sub-programs of the abstract program; a
    -- polymorphic rule (`bind`) also has its value types, monad, and instances free in the
    -- abstract side, which are fixed by unification, not synthesized. Keep only positions
    -- whose type is neither a class instance nor type-like (its `∀`-body a `Sort`).
    let avPositions ← (← mvarPositions xs a).filterM fun i => do
      unless !cPositions.contains i && i != qPosition && some i != ePosition? do return false
      let ty ← inferType xs[i]!
      if (← isClass? ty).isSome then return false
      forallTelescopeReducing ty fun _ b => return !b.isSort
    let keys ← DiscrTree.mkPath c
    return ({ declName, avPositions, qPosition, ePosition?, specificity := keys.size }, keys)

/-- The `@[ascend]` registry: specs keyed by their concrete program. -/
initialize ascendExt :
    SimpleScopedEnvExtension (SpecInfo × Array DiscrTree.Key) (DiscrTree SpecInfo) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun tree (info, keys) => tree.insertKeyValue keys info
  }

initialize registerBuiltinAttribute {
  name := `ascend
  descr := "registry of Refinement specs driving the ascend engine"
  add := fun declName _stx kind => do
    let entry ← MetaM.run' (analyzeSpec declName)
    ascendExt.add entry kind
}

/-- The specs in scope, most specific first for a given lookup. -/
def getSpecs : CoreM (DiscrTree SpecInfo) :=
  return ascendExt.getState (← getEnv)

end Ascend
