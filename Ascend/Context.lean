import Lean
import Ascend.Attr

/-!
# The engine monad and goal metadata

`AscendM` runs over `SymM`: goals are hash-consed (`preprocessMVar`), every term the engine
builds is re-shared (`shareCommonInc`), and rules apply by pattern matching, so term
comparisons and slot bindings are pointer operations rather than structural walks.

`RWPApp` is the parsed form of a goal target `pre ⊑ rwp γ a c Q E`: the engine's goal shape,
closed under every decomposition step it performs.
-/

open Lean Meta Sym

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
/-- The concrete program type `CProg`. -/
def CProg (g : RWPApp) : Expr := g.args[0]!
def CVal (g : RWPApp) : Expr := g.args[2]!
def AVal (g : RWPApp) : Expr := g.args[3]!
def CPred (g : RWPApp) : Expr := g.args[4]!
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

/-- A spec compiled to apply-ready form against a phase. -/
structure CachedRule where
  /-- The backward rule `∀ params P', (P' ⊑ pre') → P' ⊑ rwp …`: applying it to a goal
  binds the value slots by pattern matching and leaves the precondition entailment as the
  sole subgoal. -/
  rule : BackwardRule
  /-- For specs with abstract-input variables: the abstract program as a lambda over them,
  abstracted over the spec's remaining parameters. Instantiated to pre-assign a flex
  abstract slot before the rule applies. -/
  template? : Option AbstractMVarsResult

/-- Read-only engine context. -/
structure Context where
  /-- The `@[ascend]` registry in scope. -/
  specs : DiscrTree SpecInfo

/-- Mutable engine state. -/
structure State where
  /-- Verification conditions emitted so far. -/
  vcs : Array MVarId := #[]
  /-- Apply-ready rules, keyed by spec name and the goal's `WP` instances. The instances are
  keyed by pointer, sound because they are subterms of the hash-consed goal. -/
  ruleCache : Std.HashMap (Name × ExprPtr × ExprPtr) CachedRule := {}

abbrev AscendM := ReaderT Context (StateRefT State SymM)

end Ascend
