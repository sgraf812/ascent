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

/-- The `rwp γ a c Q E` on the right of an entailment, destructured. The 21 arguments are too
many for `let_expr`, so this carries them with named accessors. -/
structure RWPApp where
  /-- The `rwp` head with its levels. -/
  head : Expr
  /-- The 21 `rwp` arguments. -/
  args : Array Expr

namespace RWPApp

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

/-- Destructure an `rwp γ a c Q E` application. -/
def parseRWP? (rhs : Expr) : Option RWPApp := do
  guard <| rhs.isAppOfArity ``Ascent.rwp 21
  return { head := rhs.getAppFn, args := rhs.getAppArgs }

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
  /-- Apply-ready rules, keyed by spec name and the phase's `γ` (by pointer: the compiled
  rule pins `γ`, so every subgoal it produces carries the same object). The goal's `WP`
  instance slots are unusable as keys: rule application leaves them as fresh metavariables,
  one per node. A run mixing monad pairs under one `γ` would need the monads in the key. -/
  ruleCache : Std.HashMap (Name × ExprPtr) CachedRule := {}

abbrev AscendM := ReaderT Context (StateRefT State SymM)

end Ascend
