import Lean
import Ascend.Attr
import Lean.Elab.Tactic.Do.Internal.VCGen.LatticeOp
import Lean.Elab.Tactic.Do.Internal.VCGen.Entails

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

/-- Rebuild the `rwp` application with the abstract program replaced. -/
def withA (g : RWPApp) (a : Expr) : Expr := mkAppN g.head (g.args.set! 17 a)
/-- Rebuild the `rwp` application with the concrete program replaced. -/
def withC (g : RWPApp) (c : Expr) : Expr := mkAppN g.head (g.args.set! 18 c)

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
  /-- The lattice-connective split table (`⊓`, `⇨`, `⌜·⌝`, `⊤`, and the magic-wand residual),
  keyed by operator head. Reused from `vcgen`: `splitLatticeOp?` looks a residual precondition's
  head up here and builds its decomposition rule. -/
  latticeOps : Std.HashMap Name Lean.Elab.Tactic.Do.Internal.VCGen.LatticeOp
  /-- Pre-built backward rules driving precondition normalization and discharge (strip `⊓ ⊤`,
  lift `⌜·⌝`/bare preconditions, close reflexively, strip the `⊤ ⊑` wrapper). Reused from
  `vcgen`. -/
  backwardRules : Lean.Elab.Tactic.Do.Internal.VCGen.BackwardRules

/-- Mutable engine state. -/
structure State where
  /-- Verification conditions emitted so far. -/
  vcs : Array MVarId := #[]
  /-- Apply-ready rules, keyed by spec name and the phase's `γ` (by pointer: the compiled
  rule pins `γ`, so every subgoal it produces carries the same object). The goal's `WP`
  instance slots are unusable as keys: rule application leaves them as fresh metavariables,
  one per node. A run mixing monad pairs under one `γ` would need the monads in the key. -/
  ruleCache : Std.HashMap (Name × ExprPtr) CachedRule := {}
  /-- Apply-ready lattice-split rules, keyed by the connective's constant prefix (by pointer:
  the rule bakes in the carrier and instances) and its argument count (which fixes the operand
  and state-argument slots). The split-rule construction is reused; only the cache is ours. -/
  latticeCache : Std.HashMap (ExprPtr × Nat) BackwardRule := {}
  /-- The sub-program holes: each let-bound hole fvar paired with its web metavariable. Proof
  terms reference the fvars; the final proof substitutes all of them at once with the
  instantiated web (`Expr.replaceFVars`, one pass over the proof). -/
  holes : Array (FVarId × MVarId) := #[]

/-- Per-goal scope threaded through the worklist. Carries the most recently lifted pure
precondition so a residual `⌜φ⌝` entailment discharges against it in `O(1)` (the coupling a leaf
needs is the one its predecessor just established), rather than searching the local context. -/
structure Scope where
  /-- The most recently lifted pure precondition: its fvar paired with its instantiated type, so
  a residual `⌜φ⌝` discharges against it without re-reading and re-instantiating the type. -/
  lastLiftedPre? : Option (FVarId × Expr) := none

abbrev AscendM := ReaderT Context (StateRefT State SymM)

end Ascend
