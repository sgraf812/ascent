import Lean
import Ascend.Attr

/-!
# The engine monad and goal metadata

`AscendM` carries the spec registry and the accumulated VCs. `RWPApp` is the parsed form of a
goal target `pre ⊑ rwp γ a c Q E`: the engine's goal shape, closed under every decomposition
step it performs.
-/

open Lean Meta

namespace Ascend

/-- A goal target of the form `pre ⊑ rwp γ a c Q E`, destructured. -/
structure RWPApp where
  /-- The `⊑` head (`PartialOrder.rel` with its levels). -/
  relHead : Expr
  /-- The four `⊑` arguments: carrier, instance, precondition, right-hand side. -/
  relArgs : Array Expr
  /-- The `rwp` head with its levels. -/
  head : Expr
  /-- The 21 `rwp` arguments. -/
  args : Array Expr

namespace RWPApp

def pre (g : RWPApp) : Expr := g.relArgs[2]!
def rhs (g : RWPApp) : Expr := g.relArgs[3]!
/-- The abstract program type `AProg`, an application `AM AVal` for monadic programs. -/
def AProg (g : RWPApp) : Expr := g.args[1]!
def CVal (g : RWPApp) : Expr := g.args[2]!
def AVal (g : RWPApp) : Expr := g.args[3]!
def instWPc (g : RWPApp) : Expr := g.args[13]!
def instWPa (g : RWPApp) : Expr := g.args[14]!
def γ (g : RWPApp) : Expr := g.args[16]!
def a (g : RWPApp) : Expr := g.args[17]!
def c (g : RWPApp) : Expr := g.args[18]!
def Q (g : RWPApp) : Expr := g.args[19]!
def E (g : RWPApp) : Expr := g.args[20]!

end RWPApp

/-- Destructure a target `pre ⊑ rhs`. Returns the `rel` head and its four arguments. -/
def parseRel? (target : Expr) : Option (Expr × Array Expr) :=
  if target.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
    some (target.getAppFn, target.getAppArgs)
  else
    none

/-- Destructure a target `pre ⊑ rwp γ a c Q E`. -/
def parseRWP? (target : Expr) : Option RWPApp := do
  let (relHead, relArgs) ← parseRel? target
  let rhs := relArgs[3]!
  guard <| rhs.isAppOfArity ``Ascent.rwp 21
  return { relHead, relArgs, head := rhs.getAppFn, args := rhs.getAppArgs }

/-- Read-only engine context. -/
structure Context where
  /-- The `@[ascend]` registry in scope. -/
  specs : DiscrTree SpecInfo

/-- Mutable engine state. -/
structure State where
  /-- Verification conditions emitted so far. -/
  vcs : Array MVarId := #[]

abbrev AscendM := ReaderT Context (StateRefT State MetaM)

end Ascend
