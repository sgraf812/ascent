/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/

import Ascent.Tactic.VCGen.Shim
import Lean.Elab.Tactic.Do.VCGen.Split
import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.RuleConstruction
import Ascent.Tactic.VCGen.RuleConstruction
import Lean.Elab.Tactic.VCGen.LatticeOp
import Lean.Elab.Tactic.VCGen.Util
import Lean.Meta.Sym.InferType

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.VCGen.SpecAttr
open Lean.Elab.Tactic.VCGen

/-!
`VCGenM`-level cache wrappers around the `SymM` rule constructors in
`VCGen.RuleConstruction`.
-/

namespace Lean.Elab.Tactic.VCGen.Ascend


/--
Cached version of spec rule construction.

Both `Triple`/`⊑ wp` and equality entries go through `tryMkBackwardRuleFromSpec`, which normalizes
an equality spec to `⊑ wp` form using the supplied `wp` metadata before building the rule.

Cache key: `(proof key, ruleKey, excessArgs.size)`, where `ruleKey` is the hash-consed
`WRPApp.ruleKey` of the goal, the arguments the rule bakes in: the concrete `WP` instance, the
abstract monad, the abstract lattice types and `γ`.
-/
def mkBackwardRuleFromSpecCached (specThm : SpecTheorem) (info : WRPApp) :
    OptionT VCGenM BackwardRule := do
  let ruleKey ← shareCommon info.ruleKey
  let key := (specThm.proof.key, ExprPtr.mk ruleKey, info.excessArgs.size)
  let s := (← get).specBackwardRuleCache
  if let some rule := s[key]? then return rule
  let some rule ← withNewMCtxDepth <| tryMkBackwardRuleFromSpec specThm info |>.run
    | failure
  let rule ← rule.shareCommon
  modify fun st => { st with specBackwardRuleCache := st.specBackwardRuleCache.insert key rule }
  return rule

open Lean.Elab.Tactic.Do in
/--
Cached version of `mkBackwardRuleForSplit`.

Cache key: `(splitter name, ruleKey, excessArgs.size)`, with `ruleKey` as for spec rules.
-/
def mkBackwardRuleForSplitCached (splitInfo : SplitInfo) (info : WRPApp) :
    VCGenM BackwardRule := do
  let cacheKey := match splitInfo with
    | .ite .. => ``ite
    | .dite .. => ``dite
    | .cond .. => ``cond
    | .matcher matcherApp => matcherApp.matcherName
  let key := (cacheKey, ExprPtr.mk (← shareCommon info.ruleKey), info.excessArgs.size)
  let s := (← get).splitBackwardRuleCache
  if let some rule := s[key]? then return rule
  let rule ← mkBackwardRuleForSplit splitInfo info
  let rule ← rule.shareCommon
  modify fun st =>
    { st with splitBackwardRuleCache := st.splitBackwardRuleCache.insert key rule }
  return rule

/--
Cached construction of a lattice-split backward rule for the operator heading `rhs`. On a cache miss
the rewrite and terminal sets are assembled from the built-in seeds and the operator's `@[frameproc]`
contributions (`fp?`); a cache hit skips that work.

Cache key: the `head … cₙ` prefix built from the constant arguments (which the rule bakes in verbatim)
and the argument count (which fixes the schematic operand and state count).
-/
def mkLatticeOpRuleCached (rhs : Expr) (op : LatticeOp) :
    VCGenM BackwardRule := do
  let key := (ExprPtr.mk (rhs.getAppPrefix op.numConst), rhs.getAppNumArgs)
  if let some rule := (← get).latticeBackwardRuleCache[key]? then return rule
  let rule ← (← mkLatticeOpRule rhs op).shareCommon
  modify fun st => { st with latticeBackwardRuleCache := st.latticeBackwardRuleCache.insert key rule }
  return rule

end Lean.Elab.Tactic.VCGen.Ascend
