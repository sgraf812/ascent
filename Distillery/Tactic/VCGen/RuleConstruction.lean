/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/

import Distillery.Tactic.VCGen.Shim
import Lean.Elab.Tactic.Do.VCGen.Split
import Lean.Elab.Tactic.VCGen.Context
import Lean.Elab.Tactic.VCGen.Reduce
import Lean.Elab.Tactic.VCGen.SpecDB
import Lean.Elab.Tactic.VCGen.Util
import Lean.Elab.Tactic.VCGen.ExcessArgsFrame
import Lean.Meta.Sym.Apply
import Lean.Meta.Sym.Util
import Std.WP.Frame

open Lean Meta Elab Tactic Sym
open Lean.Elab.Tactic.VCGen.SpecAttr

namespace Lean.Elab.Tactic.VCGen.Distill


/-!
Construction of `BackwardRule`s from `SpecTheorem`s and split info, with no knowledge of `VCGenM`.
The `VCGenM` cache wrappers live in `VCGen.RuleCache`.
-/

open Std.WP Lean.Order

/-! ## Spec rules -/

/-- Build the explicit pointwise implication premise used to weaken a concrete `post`.
    State binders are named positionally from `stateArgNames` (else `s`); their names ride
    on the premise and are later introduced with the right user-facing names. -/
def mkPostPointwisePremise (postSpec postTarget postTy : Expr) (ssTypes : Array Expr)
    (stateArgNames : Array Name := #[]) : MetaM Expr := do
  let .forallE _ α (.forallE _ β _ _) _ := postTy
    | throwError "expected a return relation, got {indentExpr postTy}"
  withLocalDeclD `cv α fun cv => do
  withLocalDeclD `av β fun av => do
    let ssNamesTypes := ssTypes.mapIdx fun i ty => (stateArgNames[i]?.getD `s, ty)
    withLocalDeclsDND ssNamesTypes fun ss' => do
      let lhs := postSpec.betaRev <| ss'.reverse ++ #[av, cv]
      let rhs := mkAppN (mkApp2 postTarget cv av) ss'
      mkForallFVars (#[cv, av] ++ ss') (← mkAppM ``PartialOrder.rel #[lhs, rhs])

/-- Reduce a projection of a constructor application, e.g. `(⟨R⟩ : Thrown).onThrow` to `R`.
Return any other term unchanged. -/
def reduceProjOfCtor (e : Expr) : MetaM Expr := do
  let .const fn _ := e.getAppFn | return e
  let some info ← getProjectionFnInfo? fn | return e
  let args := e.getAppArgs
  let some s := args[info.numParams]? | return e
  let some f ← projectCore? s.consumeMData info.i | return e
  return mkAppN f (args.extract (info.numParams + 1)) |>.headBeta

/-- Build the pointwise premise `spec ⊑ target` for a component of an exception relation, whose
type `ty` ends in `nState` state arguments. A relation `εc → εa → σ → Prop` binds the concrete and the
abstract exception, and a component `εc → σ → Prop` of a concrete-only layer binds the concrete
exception. -/
def mkERelPointwisePremise (spec target ty : Expr) (nState : Nat)
    (stateArgNames : Array Name := #[]) : MetaM Expr := do
  let ty ← whnfR ty
  let (nExc, ssTypes) ← forallTelescopeReducing ty fun xs _ => do
    let nExc := xs.size - nState
    return (nExc, ← (xs.drop nExc).mapM (Meta.inferType ·))
  if nExc == 2 then
    return ← mkPostPointwisePremise spec target ty ssTypes stateArgNames
  let .forallE _ α _ _ := ty
    | throwError "expected an exception relation, got {indentExpr ty}"
  withLocalDeclD `ec α fun ec => do
    let ssNamesTypes := ssTypes.mapIdx fun i t => (stateArgNames[i]?.getD `s, t)
    withLocalDeclsDND ssNamesTypes fun ss' => do
      let lhs := (mkAppN spec (#[ec] ++ ss')).headBeta
      let rhs := mkAppN target (#[ec] ++ ss')
      mkForallFVars (#[ec] ++ ss') (← mkAppM ``PartialOrder.rel #[lhs, rhs])

/-- Recursively decompose `epostsSpec ⊑ epostsAbstract` into per-component proofs.
    - `(head, tail)` → mvar for `head ⊑ epostsAbstract.fst`, recurse on `tail`
    - Otherwise, if `EPosts` is a product, project `epostsSpec.fst`/`.snd` and decompose those
    - Otherwise, if `EPosts` is `Unit`, trivial via `Unit.unit_le`
    - Otherwise, if `EPosts` is a function type, a pointwise mvar
    - Otherwise, if `EPosts` has a `ToEStack` instance, decompose the entailment between the
      stacks and reflect it via `ToEStack.le_of_toEStack_le`
    - Otherwise → single mvar for `epostsSpec ⊑ epostsAbstract` -/
partial def decomposeProdRel (EPosts epostsSpec epostsAbstract : Expr) (nState : Nat)
    (stateArgNames : Array Name := #[]) : MetaM Expr := do
  match_expr epostsSpec with
  | Prod.mk ehTy etTy head tail =>
    let absHead ← mkAppM ``Prod.fst #[epostsAbstract]
    let absTail ← mkAppM ``Prod.snd #[epostsAbstract]
    let hTail ← decomposeProdRel etTy tail absTail nState stateArgNames
    -- The components of a `toEStack` image are projections such as `(⟨R⟩ : Thrown).onThrow`.
    let head ← reduceProjOfCtor head
    /- Sometimes, even though `eposts` is not schematic itself, its components might be schematic.
      Think of a triple of a kind `⦃ pre ⦄ x ⦃ post; eposts₁, ⊥, eposts₃, ⊥, ... ⦄`.
      In this case we do not want to create new metavariables for `eposts₁`, `eposts₃`, etc.
      Instead, we will just assign them to `epostsAbstract.snd.fst` and
      `epostsAbstract.snd.snd.fst`, etc. -/
    if head.isMVar then
      head.mvarId!.assign absHead
      mkAppM ``Prod.mk_le_snd #[tail, epostsAbstract, hTail]
    else
      let headTy ← Meta.inferType head
      let hHeadTy ← mkERelPointwisePremise head absHead headTy nState stateArgNames
      let hHead ← mkFreshExprMVar (userName := `epostsImpl) hHeadTy
      mkAppM ``Prod.mk_le #[head, tail, epostsAbstract, hHead, hTail]
  | _ =>
    let EPosts := EPosts.consumeMData
    match_expr EPosts with
    | Prod ehTy etTy =>
      let specHead ← mkAppM ``Prod.fst #[epostsSpec]
      let specTail ← mkAppM ``Prod.snd #[epostsSpec]
      let absHead ← mkAppM ``Prod.fst #[epostsAbstract]
      let absTail ← mkAppM ``Prod.snd #[epostsAbstract]
      let headTy ← Meta.inferType specHead
      let hHeadTy ← mkERelPointwisePremise specHead absHead headTy nState stateArgNames
      let hHead ← mkFreshExprMVar (userName := `epostsImpl) hHeadTy
      let hTail ← decomposeProdRel etTy specTail absTail nState stateArgNames
      mkAppM ``Prod.mk_le #[specHead, specTail, epostsAbstract, hHead, hTail]
    | _ =>
      let EPostsR ← whnfR EPosts
      -- The terminator is reducibly `PUnit`, under any of its names.
      if EPostsR.isConstOf ``PUnit then
        mkAppM ``Unit.unit_le #[epostsAbstract]
      else if EPostsR.isForall then
        -- A bare relation, e.g. of `Except ε`, yields a pointwise VC like a stack component.
        let hTy ← mkERelPointwisePremise epostsSpec epostsAbstract EPostsR nState stateArgNames
        let h ← mkFreshExprMVar (userName := `epostsImpl) hTy
        mkExpectedTypeHint h (← mkAppM ``PartialOrder.rel #[epostsSpec, epostsAbstract])
      else if let some (args, inst) ← synthInstanceOpt? ``ToEStack #[some EPosts] then
        let args := args.push inst
        let toEStack ← mkAppOptM ``ToEStack.toEStack (args.map some)
        -- `unfoldProjInst?` turns the image of a spec literal into a stack literal.
        let stackSpec := mkApp toEStack epostsSpec
        let stackAbstract := mkApp toEStack epostsAbstract
        let h ← decomposeProdRel args[1]! ((← unfoldProjInst? stackSpec).getD stackSpec)
          stackAbstract nState stateArgNames
        withDefault <| mkAppOptM ``ToEStack.le_of_toEStack_le <|
          (args.map some) ++ #[some epostsSpec, some epostsAbstract, some h]
      else
        let hTy ← mkAppM ``PartialOrder.rel #[epostsSpec, epostsAbstract]
        mkFreshExprMVar (userName := `epostsImpl) hTy

/--
Create the proof term for the backward rule built from an instantiated spec theorem.
In order for the backward rule to apply, the concrete precondition, postcondition and exception
postcondition appearing in the spec may need to be generalized into rule parameters, emitting
verification conditions for the generalization.

### General idea

Consider the spec theorem `WPMonad.bind_le_wp_bind`:
```
WPMonad.bind_le_wp_bind :
  wp x (fun a => wp (f a) post eposts) eposts ⊑ wp (x >>= f) post eposts
```
This theorem is already in WP-form, so `post` and `eposts` are schematic. However, its precondition
`wp x (fun a => wp (f a) post eposts) eposts` is not. Hence we must emit a VC for the precondition:
```
prf : ∀ {α β} (x : m α) (f : α → m β) (post : β → Pred) (eposts : EPosts)
  (pre : Pred) (hpre : pre ⊑ wp x (fun a => wp (f a) post eposts) eposts),
  pre ⊑ wp (x >>= f) post eposts
```
The proof term is constructed with `PartialOrder.rel_trans hpre WPMonad.bind_le_wp_bind`.

#### Postcondition VCs

Similarly, a VC is generated for the postcondition if it is not schematic. For example, a
hypothetical restrictive spec for `pure` could be:
```
myPure.spec (n : Nat) : (⊤ : Prop) ⊑ wp (myPure n) (fun r => r = n) eposts
```
This yields a backward rule of the form:
```
prf : ∀ (n : Nat) (pre : Prop) (hpre : pre ⊑ True)
  (post : Nat → Prop) (hpost : ∀ r, r = n ⊑ post r) (eposts : Unit),
  pre ⊑ wp (myPure n) post eposts
```
The postcondition VC is pointwise over the return value and over any excess state arguments. The
proof is generalized with `WP.wp_monotone_post_le`.

#### Exception postcondition VCs

A VC is also generated for the exception postcondition if it is not schematic. For a product
value, the relation `epostsSpec ⊑ eposts` is decomposed component by component:
```
∀ e s₁ ... sₙ, epostsSpec.fst e s₁ ... sₙ ⊑ eposts.fst e s₁ ... sₙ
```
and recursively for the tail. `decomposeProdRel` assembles these component VCs using
`Prod.mk_le` and `Unit.unit_le`. A bare function value such as the one of `Except ε` yields the
same pointwise VC. A value of a type with a `ToEStack` instance is first converted to a stack.
The proof is then generalized with `WP.wp_monotone_epost_le`. When the spec exception
postcondition is `⊥`, no VC is needed and `WP.wp_monotone_bot_le` is used instead.

#### Excess state arguments

Furthermore, when there are excess state arguments `[s₁, ..., sₙ]` involved, the proof is
specialized to those arguments:
```
... :
  pre ⊑ wp x (fun a => wp (f a) post eposts) eposts s₁ ... sₙ →
  pre ⊑ wp (x >>= f) post eposts s₁ ... sₙ
```
The precondition and all generated pointwise postcondition premises are applied to these same state
arguments.

### Caching

It turns out we can cache backward rules for the cache key
`(specThm.proof.key, instWP, excessArgs.size)`. This is important for performance and helps avoid
rebuilding the same rule for every goal that uses the same spec theorem, `WPMonad` instance and
number of excess state arguments. We do that in the `VCGenM` wrapper
`mkBackwardRuleFromSpecCached`.

The rule is built from the abstracted proof returned here via `mkBackwardRuleFromExpr`. This keeps
the proof construction reusable even when the proof still contains free variables from the goal
context, such as generic monad or WP instance parameters.

### Specialization

It is unnecessary to use the `bind` rule in full generality. It is much more efficient to specialize
it for the particular predicate type, exception postcondition type and `WPMonad` instance.
`tryMkBackwardRuleFromSpec` does that by instantiating the spec theorem and checking that its
`Pred` and `WPMonad` arguments match the ones from the use site.

For `StateM Nat` and one excess state arg `s`, the type produced for `WPMonad.bind_le_wp_bind` becomes
```
prf : ∀ (pre : Prop) (α : Type) (x : StateT Nat Id α) (β : Type)
  (f : α → StateT Nat Id β) (post : β → Nat → Prop) (eposts : Unit) (s : Nat),
  pre ⊑ wp x (fun a => wp (f a) post eposts) eposts s →
  pre ⊑ wp (x >>= f) post eposts s
```
-/
def mkSpecBackwardProof (info : WRPApp)
    (pre prog postSpec epostsSpec specProof : Expr) (ss ssTypes : Array Expr)
    (stateArgNames : Array Name := #[]) : MetaM AbstractMVarsResult := do
  /- we start with `pre ⊑ wp prog post eposts` where
  1. `pre` represents the Lean expression for `pre`
  2. `prog`, `postSpec`, and `epostsSpec` are the selected arguments of the spec's `wp` RHS
  3. `specProof` is the proof of the spec `pre ⊑ wp prog postSpec epostsSpec`
  4. `ss` represents the Lean expressions for the state variables `s1`, `s2`, ..., `sn`
  5. `ssTypes` represents the Lean types for the state variables `s1`, `s2`, ..., `sn` -/
  let wpArgs := info.lemmaPrefix
  let wpLemma (n : Name) := mkAppN (mkConst n info.head.constLevels!) wpArgs
  let mut postAbstract := postSpec.consumeMData
  let mut epostsAbstract := epostsSpec.consumeMData
  let mut specApplied := specProof

  /- abstract concrete `post` if it is not already abstract -/
  unless postAbstract.isMVar do
    /- `α → Pred`: type of `post` -/
    let postTy ← Meta.inferType postSpec
    /- mvar `postAbstract` for new abstract `post` -/
    postAbstract ← mkFreshExprMVar (userName := `Post) postTy
    /- premise type `∀ (a : α) (s₁ : σ₁) ... (sₙ : σₙ), postSpec a s₁ ... sₙ → postAbstract a s₁ ... sₙ` -/
    let hpostTy ← mkPostPointwisePremise postSpec postAbstract postTy ssTypes stateArgNames
    /- mvar `?postImpl` for the proof of the premise -/
    let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
    /- `wp_monotone_post_le` expects its premise at the *function-lattice* order `postSpec ⊑ postAbstract`,
       whereas `hpost` is stated pointwise (`∀ a s…, postSpec a s… ⊑ postAbstract a s…`). The two are
       defeq, but unfolding the function-lattice `⊑` instance is blocked when the post's domain is a
       metavariable (e.g. the accumulator `β` of a `forIn` loop spec). Cast `hpost` to the function
       order here so the defeq is forced at this depth, keeping the user-facing VC pointwise. -/
    let relTy ← mkAppM ``PartialOrder.rel #[postSpec, postAbstract]
    let hpostRel ← mkExpectedTypeHint hpost relTy
    /- get the proof of `pre ⊑ wp prog postAbstract epostsSpec`, where `post` is abstracted.
       Uses wp_monotone_post_le: post ⊑ post' → pre ⊑ wp x post eposts → pre ⊑ wp x post' eposts -/
    specApplied := mkAppN (wpLemma ``Distillery.wrp_mono_post_le)
      #[prog, postSpec, postAbstract, epostsSpec, hpostRel, pre, specApplied]

  /- abstract concrete `eposts` if it is not already abstract -/
  unless epostsAbstract.isMVar do
    /- `EStack⟨t₁, t₂, ..., tₙ⟩`: type of `eposts` -/
    let epostsTy ← Meta.inferType epostsSpec
    /- mvar `epostsAbstract` for new abstract `eposts` -/
    epostsAbstract ← mkFreshExprMVar (userName := `EPosts) epostsTy
    /- if `eposts` is `⊥`, then `eposts ⊑ epostsAbstract` holds trivially and
      abstracting `eposts` can be simply done by `WP.wp_monotone_bot_le` without
      introducing a new premise. This case is quite common, that's why we handle
      it specially.
      The test runs at a fresh metavariable depth, where a schematic component of
      `eposts` such as `E` in `estack⟨E⟩` is read-only. `decomposeProdRel` below
      assigns `E` the matching component of `epostsAbstract`. -/
    let isBot ← withNewMCtxDepth do
      try
        let botEPred ← mkAppOptM ``Lean.Order.bot #[epostsTy, none]
        isDefEqGuarded epostsSpec botEPred
      catch _ => pure false
    if isBot then
      /- get the proof of `pre ⊑ wp prog postAbstract epostsAbstract`, where `eposts (= ⊥)` is abstracted.
        This proof DOES NOT have a `?epostsImpl` premise -/
      specApplied := mkAppN (wpLemma ``Distillery.wrp_mono_bot_le)
        #[prog, postAbstract, epostsAbstract, pre, specApplied]
    else
      /- Decompose `epostsSpec ⊑ epostsAbstract` into per-component proofs
        using `Prod.mk_le` and `Unit.unit_le` -/
      let heposts ← decomposeProdRel info.EPosts epostsSpec epostsAbstract ss.size stateArgNames
      specApplied := mkAppN (wpLemma ``Distillery.wrp_mono_erel_le)
        #[prog, postAbstract, epostsSpec, epostsAbstract, heposts, pre, specApplied]

  /- By default we always abstract `pre`, since in most of the specifications
    `pre` is not schematic. In exceptional cases, where `pre` is schematic, it
    is redundant, but we still do that to keep the code simple.

    Here we also apply the excess state arguments to `pre` and `wp prog postAbstract epostsAbstract` -/
  /- use `beta` to create `pre s₁ ... sₙ`  to avoid creating beta redexes when `pre` is a lambda -/
  let preApplied := pre.beta ss
  /- proof of the original theorem with abstracted `post` and `eposts` specialized to the excess state arguments -/
  specApplied := mkAppN specApplied ss
  /- `wp prog postAbstract epostsAbstract s₁ ... sₙ` -/
  let wpTy := mkAppN info.head <|
    info.args.take 18 ++ #[prog, info.abs, postAbstract, epostsAbstract] ++ ss
  let specAppliedTy ← mkAppM ``PartialOrder.rel #[preApplied, wpTy]
  /- later when the whole proof is type checked, we want to help the kernel by providing the expected type -/
  specApplied ← mkExpectedTypeHint specApplied specAppliedTy
  let preAppliedTy ← Meta.inferType preApplied
  /- create a new mvar for the abstracted `pre` -/
  let preAbstract ← mkFreshExprMVar (userName := `Pre) preAppliedTy
  let specAbstractTy ← mkAppM ``PartialOrder.rel #[preAbstract, preApplied]
  /- create a new mvar for the proof of the abstracted `pre` -/
  let specAbstract ← mkFreshExprMVar (userName := `vc) specAbstractTy
  /- use `PartialOrder.rel_trans` to compose the abstracted `pre` and the proof of the original theorem -/
  specApplied ← mkAppM ``PartialOrder.rel_trans #[specAbstract, specApplied]

  abstractMVars specApplied

/--
Normalize an instantiated equality spec `lhs = rhs` (both of type `info.M α`) to the `⊑ wp` form
`wp rhs Q E ⊑ wp lhs Q E` by instantiating `wp_le_wp_of_eq` with fresh schematic `Q`/`E`.

The schematic `Q`/`E` make the postcondition and exception-postcondition VCs collapse in
`mkSpecBackwardProof`, so the resulting rule rewrites a `wp lhs` goal to a `wp rhs` premise, matching
the equational behaviour of a simp spec. Only the monad, the value type and the `WP` instance are
pinned from the goal, mirroring how `tryMkBackwardRuleFromSpec` treats `⊑ wp` specs; the equation's
remaining variables, including instance binders, stay schematic and become rule parameters that
applying the rule binds against the concrete goal program. Dictionary projections this substitution
exposes in the premise program (e.g. for class projection unfold equations like
`MonadState.modifyGet.eq_1`) are reduced by `wpHeadReduce?` before the next spec lookup.
-/
def eqSpecToWp? (info : WRPApp) (eqPrf eqType : Expr) :
    OptionT MetaM (Expr × Expr) := do
  let_expr Eq eqα _lhs _rhs := eqType
    | throwError "simp spec is not an equation: {eqType}"
  -- Unify the equation's type with the goal's program type. First-order approximation decomposes
  -- flex-headed equation types (e.g. class projection unfold equations quantified over the monad,
  -- like `MonadState.modifyGet.eq_1`, where `eqα = ?m ?β`). The unification must happen at the
  -- current metavariable depth: `mkAppOptM` raises the depth, so the equation's type metavariables
  -- are read-only there.
  guard <| ← withReducible <| approxDefEq <| isDefEqGuarded eqα info.Prog
  -- `post`/`eposts` are schematic metavariables (their VCs collapse downstream).
  let post ← mkFreshExprMVar (userName := `Q) (← mkArrow info.Value (← mkArrow info.AValue info.Pred))
  let eposts ← mkFreshExprMVar (userName := `E) info.EPosts
  -- The goal's leading `wp` arguments `#[Prog, Value, Pred, EPosts, instAL, instEAL, instWP]` are
  -- exactly the leading arguments of `wp_le_wp_of_eq`.
  -- The abstract program is schematic, so that the rule does not capture the goal's hole.
  let abs ← mkFreshExprMVar (userName := `a) info.args[1]!
  let specProof ← mkAppOptM ``Distillery.wrp_le_wrp_of_eq <|
    (info.lemmaPrefix).map some ++ #[none, none, some eqPrf, some post, some eposts]
  return (specProof, ← instantiateMVars (← Meta.inferType specProof))

/--
Try to build a backward rule from a single spec theorem.

For a spec already in `⊑ wp` form (`pre ⊑ wp prog post eposts`, where the lattice type is
`info.Pred = σ1 → ... → σn → Prop`), produces an auxiliary lemma directly. An equality spec
`lhs = rhs` is first normalized to `wp rhs Q E ⊑ wp lhs Q E` via `eqSpecToWp?` and then handled the
same way.

- `info.Pred`: the goal's lattice type (e.g. `Nat → Prop`)
- `info.instWP`: the `WP` instance of the goal's `wp` application
- `info.excessArgs`: free variables representing state args from
  `info.Pred = σ1 → ... → σn → Prop`
-/
def tryMkBackwardRuleFromSpec (specThm : SpecTheorem) (info : WRPApp)
    (stateArgNames : Array Name := #[]) : OptionT MetaM BackwardRule := do
  -- The rule takes the concrete side of the goal verbatim, as core does. On the abstract side the
  -- value type, the `WP` instance and the program are replaced by metavariables that become rule
  -- parameters.
  let goalInfo := info
  let info ← info.schematic
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (_xs, _bs, specProof, specType) ← specThm.instantiate
  -- Equality specs (the simp side of `@[spec]`) are normalized to `⊑ wp` form, then handled like
  -- any ordinary `⊑ wp` spec.
  let (specProof, specType) ←
    if specType.isAppOfArity ``Eq 3 then eqSpecToWp? info specProof specType
    else pure (specProof, specType)
  let_expr PartialOrder.rel Pred' _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  guard <| ← isDefEqGuarded info.Pred Pred'
  let some specInfo := isWRPApp? rhs
    | throwError "target not a wrp application {rhs}"
  let prog := specInfo.prog
  let postSpec := specInfo.post
  let epostsSpec := specInfo.eposts
  -- The abstract types and `γ` of the spec are unified with the goal's schematic prefix, then the
  -- concrete `WP` instance with the goal's, as core's guard, then the spec's instance binders whose
  -- types are closed by then are synthesized, then the remaining instances, at default
  -- transparency, since the goal can carry a registered instance (e.g. `Id.wpInst`) while the spec
  -- spells `WPMonad.toWP ?inst`. An argument the goal fixes must unify, or the spec does not apply
  -- to the goal. An argument the goal leaves open, such as an abstract monad that a leaf spec
  -- fixes, keeps the spec's spelling when it does not unify, and the matcher assigns the goal's
  -- metavariable when the rule applies. Sym's matcher never binds a pattern variable to a partial
  -- application, so a fixed monad must be baked in before the pattern is built. The conclusion
  -- carries the goal's arguments wherever they unified, as the goals of the run spell them.
  let mut args := info.args
  let unify (i : Nat) : OptionT MetaM Bool := do
    let ok ← if i ≥ 9 && i ≤ 16 then withDefault <| isDefEqGuarded specInfo.args[i]! info.args[i]!
      else withReducible <| approxDefEq <| isDefEqGuarded specInfo.args[i]! info.args[i]!
    if !ok && !goalInfo.args[i]!.hasExprMVar then failure
    return ok
  for i in [1, 3, 5, 7, 8, 17] do
    unless ← unify i do args := args.set! i specInfo.args[i]!
  guard <| ← withDefault <| isDefEqGuarded specInfo.args[13]! info.args[13]!
  for x in _xs, b in _bs do
    if b.isInstImplicit && !(← x.mvarId!.isAssigned) then
      let ty ← instantiateMVars (← Meta.inferType x)
      unless ty.hasExprMVar do
        if let some inst ← (monadLift (Meta.synthInstance? ty) : OptionT MetaM (Option Expr)) then
          discard <| isDefEqGuarded x inst
  for i in [10, 12, 14, 15, 16] do
    unless ← unify i do args := args.set! i specInfo.args[i]!
  let info := { info with head := specInfo.head, args := args.take 18 ++ specInfo.args.extract 18 22 }
  -- Use local excess-state binders so explicit post premises can be re-lifted to `⊑`.
  -- Name them positionally from `stateArgNames` (else `s`) so the rule's binders carry good names.
  let mut ss := #[]
  let mut ssTypes := #[]
  for h : i in [0:info.excessArgs.size] do
    let ty ← Meta.inferType info.excessArgs[i]
    ssTypes := ssTypes.push ty
    ss := ss.push <| ← mkFreshExprMVar (userName := stateArgNames[i]?.getD `s) ty
  let res ← mkSpecBackwardProof info pre prog postSpec epostsSpec specProof ss ssTypes stateArgNames
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

/-! ## Split rules -/

open Lean.Elab.Tactic.Do in
/-- The abstract program of a two-sided split: the split of the concrete program `abstractInfo`
over fresh abstract branches of type `aTy`, which `k` receives as free variables. A matcher splits
on its discriminants into fresh abstract alternatives. A matcher that eliminates only into `Prop`
keeps the abstract program `a`. -/
def withAbstractBranches {α : Type} [Inhabited α] (abstractInfo : SplitInfo) (aTy a : Expr)
    (k : Expr → Array Expr → MetaM α) : MetaM α := do
  let u ← getLevel aTy
  match abstractInfo with
  | .ite e =>
    withLocalDeclD `at aTy fun bt => withLocalDeclD `ae aTy fun ae =>
      k (mkApp5 (mkConst ``ite [u]) aTy (e.getArg! 1) (e.getArg! 2) bt ae) #[bt, ae]
  | .dite e =>
    let c := e.getArg! 1
    let tTy ← mkArrow c aTy
    let eTy ← mkArrow (mkNot c) aTy
    withLocalDeclD `at tTy fun bt => withLocalDeclD `ae eTy fun ae =>
      k (mkApp5 (mkConst ``dite [u]) aTy c (e.getArg! 2) bt ae) #[bt, ae]
  | .cond e =>
    withLocalDeclD `at aTy fun bt => withLocalDeclD `ae aTy fun ae =>
      k (mkApp4 (mkConst ``cond [u]) aTy (e.getArg! 1) bt ae) #[bt, ae]
  | .matcher m =>
    -- The same matcher over the same discriminants, into the abstract program type, with one fresh
    -- abstract alternative over the pattern variables of each concrete alternative.
    let some uPos := m.uElimPos? | k a #[]
    let motive ← lambdaTelescope m.motive fun ys _ => mkLambdaFVars ys aTy
    let altTypes ← (m.alts.zip m.altNumParams).mapM fun (alt, n) => do
      forallBoundedTelescope (← inferType alt) (some n) fun zs _ => mkForallFVars zs aTy
    withLocalDeclsDND (altTypes.mapIdx fun i t => ((`alt).appendIndexAfter (i + 1), t)) fun alts =>
      k { m with matcherLevels := m.matcherLevels.set! uPos u, motive, alts }.toExpr alts

/-- The `dite` chain of a matcher `m` on one discriminant whose alternatives have closed patterns
`p₁, …, pₙ`, and at most a final alternative whose pattern is a variable. For
`match d with | 0 => A | 1 => B | x => C x`, with the alternatives `alts = #[a₁, a₂, a₃]`, `rhs` is
`fun ps T d alts => if h : d = 0 then a₁ () else if h : d = 1 then a₂ () else a₃ d`, and `proof`
proves `m ps (fun _ => T) d alts = rhs ps T d alts`. The parameters of `m` are `ps`, and its constant
motive returns `T`. Without a final variable pattern, the last alternative is the last `else`. The
`dite`s decide by `Classical.propDecidable`. Both terms abstract the level parameters
`levelParams` of `m`. -/
structure MatchChain where
  levelParams : List Name
  rhs : Expr
  proof : Expr
  deriving Inhabited

/-- The equation `eqn` of a matcher at the universe levels `us`, the parameters `ps`, the motive
`motive` and the alternatives `alts`: the pattern of its alternative and the proof of the equation.
The pattern variable of the alternative, if any, becomes `z?`. The hypotheses `hyps` prove the
overlap hypotheses of the equation. -/
def matchEqnInstance (eqn : Name) (us : List Level) (ps : Array Expr) (motive : Expr)
    (alts : Array Expr) (z? : Option Expr) (hyps : Array Expr) : MetaM (Option (Expr × Expr)) := do
  let eqnC := mkConst eqn us
  let (mvs, _, ty) ← forallMetaTelescope (← inferType eqnC)
  let some (_, lhs, _) := ty.eq? | return none
  let args := lhs.getAppArgs
  unless args.size == ps.size + 2 + alts.size do return none
  for (a, b) in args.zip (ps ++ #[motive]) ++ (args.extract (ps.size + 2)).zip alts do
    unless ← isDefEq a b do return none
  let pat := args[ps.size + 1]!
  if let some z := z? then
    unless pat.isMVar && (← isDefEq pat z) do return none
  for mv in mvs do
    let mv := mv.mvarId!
    if ← mv.isAssigned then continue
    let mvTy ← mv.getType
    let some h ← hyps.findM? fun h => do isDefEq (← inferType h) mvTy | return none
    mv.assign h
  let pat ← instantiateMVars pat
  let prf ← instantiateMVars (mkAppN eqnC mvs)
  if pat.hasExprMVar || prf.hasExprMVar then return none
  return some (pat, prf)

/-- The `MatchChain` of the matcher `matcherName`, if it has one discriminant without an equation
name, closed patterns, and at most a final variable pattern. The equation of a closed pattern `pᵢ`
proves the branch `h : d = pᵢ`. The equation of the variable pattern proves the last branch, with
the negated conditions of the earlier branches as its overlap hypotheses. Without a variable
pattern, the matcher eliminates `d` into `Prop` for the last branch: the alternative of `pⱼ` with
`j < n` contradicts the negated condition `¬ pⱼ = pⱼ`, and the alternative of `pₙ` is its equation. -/
def mkMatchChain (matcherName : Name) : MetaM (Option MatchChain) := do
  let some info ← getMatcherInfo? matcherName | return none
  let some uPos := info.uElimPos? | return none
  let n := info.altInfos.size
  unless info.numDiscrs == 1 && info.discrInfos.all (·.hName?.isNone) && n > 0 do return none
  let catchAll := info.altInfos[n - 1]!.numFields == 1
  for i in [:n] do
    let a := info.altInfos[i]!
    unless (a.numFields == 0 && a.hasUnitThunk) || (i + 1 == n && catchAll) do return none
  let cinfo ← getConstInfo matcherName
  let lps := cinfo.levelParams
  let us := lps.map mkLevelParam
  let us0 := us.set uPos Level.zero
  let eqns := (← Match.getEquationsFor matcherName).eqnNames
  unless eqns.size == n do return none
  forallBoundedTelescope cinfo.type info.numParams fun ps mty => do
  let .forallE _ (.forallE _ D _ _) _ _ := mty | return none
  withLocalDeclD `T (mkSort us[uPos]!) fun T => do
  withLocalDeclD `d D fun d => do
  let unit := mkConst ``Unit.unit
  let altTys ← info.altInfos.mapM fun a =>
    if a.numFields == 0 then mkArrow (mkConst ``Unit) T else mkArrow D T
  withLocalDeclsDND (altTys.mapIdx fun i t => ((`alt).appendIndexAfter (i + 1), t)) fun alts => do
  let motive := mkLambda `x .default D T
  let lhsOf (z : Expr) := mkAppN (mkConst matcherName us) (ps ++ #[motive, z] ++ alts)
  -- The closed patterns, with their equations.
  let mut pats := #[]
  let mut eqPrfs := #[]
  for i in [:if catchAll then n - 1 else n] do
    let some (p, prf) ← matchEqnInstance eqns[i]! us ps motive alts none #[] | return none
    pats := pats.push p
    eqPrfs := eqPrfs.push prf
  let rhsN := if catchAll then mkApp alts[n - 1]! d else mkApp alts[n - 1]! unit
  -- The proof of `lhsOf d = rhsN` under the negated conditions `hnegs` of the earlier branches.
  let lastProof (hnegs : Array Expr) : MetaM (Option Expr) := do
    if catchAll then
      return (← matchEqnInstance eqns[n - 1]! us ps motive alts (some d) hnegs).map (·.2)
    -- Without a variable pattern, eliminate `d` by the matcher into `Prop`, with the motive
    -- `fun z => ¬ z = p₁ → … → lhsOf z = rhsN`.
    let negTys (z : Expr) : MetaM (Array Expr) :=
      (pats.extract 0 (n - 1)).mapM fun p => return mkNot (← mkEq z p)
    let motiveP ← withLocalDeclD `z D fun z => do
      withLocalDeclsDND ((← negTys z).map (`h, ·)) fun hs => do
      mkLambdaFVars #[z] (← mkForallFVars hs (← mkEq (lhsOf z) rhsN))
    let mut altsP := #[]
    for j in [:n] do
      let pj := pats[j]!
      let some alt ← withLocalDeclD `u (mkConst ``Unit) fun u => do
          withLocalDeclsDND ((← negTys pj).map (`h, ·)) fun hs => do
          let goalTy ← mkEq (lhsOf pj) rhsN
          let body? ← if j + 1 == n then
              pure <| (← matchEqnInstance eqns[j]! us ps motive alts none hs).map (·.2)
            else
              pure <| some (← mkFalseElim goalTy (mkApp hs[j]! (← mkEqRefl pj)))
          body?.mapM (mkLambdaFVars (#[u] ++ hs))
        | return none
      altsP := altsP.push alt
    return some <| mkAppN (mkConst matcherName us0) (ps ++ #[motiveP, d] ++ altsP ++ hnegs)
  -- The chain from the last alternative back to the first, under the negated conditions `hnegs`.
  let conds ← (pats.extract 0 (n - 1)).mapM (mkEq d)
  withLocalDeclsDND (conds.map (`h, mkNot ·)) fun hnegs => do
  let some prfN ← lastProof hnegs | return none
  let mut rhs := rhsN
  let mut prf := prfN
  for i' in [:n - 1] do
    let i := n - 2 - i'
    let c := conds[i]!
    let rhsT := mkApp alts[i]! unit
    let inst := mkApp (mkConst ``Classical.propDecidable) c
    let tFn ← withLocalDeclD `h c fun h => mkLambdaFVars #[h] rhsT
    let e ← mkLambdaFVars #[hnegs[i]!] rhs
    let hdE ← mkAppOptM ``dite_eq_right #[c, inst, hnegs[i]!, T, tFn, e]
    let neg ← mkLambdaFVars #[hnegs[i]!] (← mkEqTrans prf (← mkEqSymm hdE))
    rhs ← mkAppOptM ``dite #[T, c, inst, tFn, e]
    let pos ← withLocalDeclD `h c fun h => do
      let ctx ← withLocalDeclD `z D fun z => do mkLambdaFVars #[z] (← mkEq (lhsOf z) rhsT)
      let hT ← mkEqMPR (← mkCongrArg ctx h) eqPrfs[i]!
      let hdT ← mkAppOptM ``dite_eq_left #[c, inst, h, T, tFn, e]
      mkLambdaFVars #[h] (← mkEqTrans hT (← mkEqSymm hdT))
    prf := mkApp4 (mkConst ``Classical.byCases) c (← mkEq (lhsOf d) rhs) pos neg
  check prf
  unless ← isDefEq (← inferType prf) (← mkEq (lhsOf d) rhs) do return none
  let xs := ps ++ #[T, d] ++ alts
  return some { levelParams := lps, rhs := ← mkLambdaFVars xs rhs, proof := ← mkLambdaFVars xs prf }

open Lean.Elab.Tactic.Do in
/-- Creates a reusable backward rule for splitting `ite`, `dite`, `cond`, or matchers.

Uses `SplitInfo.withAbstract` to introduce abstract fvars for the split components,
then `SplitInfo.splitWith` to build the splitting proof. Hypothesis types are
discovered via `rwIfOrMatcher` inside the splitter telescope. An `ite`, `dite`, `cond` or matcher
splits both programs on the same condition or discriminants: the abstract program of the conclusion
is the same split over fresh abstract branches, one for each alternative. -/
def mkBackwardRuleForSplit
    (splitInfo : SplitInfo) (info : WRPApp) : MetaM BackwardRule := do
  -- The split value type is the goal's, so reuse the goal's program type and `WP` instance directly.
  let a := info.Value
  let ma := info.Prog
  let prf ←
    splitInfo.withAbstract ma fun abstractInfo splitFVars => do
    -- Eta-reduce matcher alts for the backward rule pattern to avoid expensive
    -- higher-order unification. The alts are eta-expanded by `withAbstract` so that
    -- `splitWith`/`matcherApp.transform` can `instantiateLambda` them directly.
    let concreteProg := match abstractInfo with
      | .ite e | .dite e | .cond e => e
      | .matcher matcherApp =>
        { matcherApp with alts := matcherApp.alts.map Expr.eta }.toExpr
    withAbstractBranches abstractInfo info.args[1]! info.abs fun abstractProg absFVars => do
    let excessArgNamesTypes ← info.excessArgs.mapM fun arg =>
      return (`s, ← Meta.inferType arg)
    withLocalDeclsDND excessArgNamesTypes fun ss => do
    withLocalDeclD `Post (← mkArrow info.Value (← mkArrow info.AValue info.Pred)) fun post => do
    withLocalDeclD `EPosts info.EPosts fun eposts => do
    let mkWP (prog abs : Expr) : Expr :=
      let args := ((info.args.set! 18 prog).set! 19 abs |>.set! 20 post).set! 21 eposts
      mkAppN (mkAppN info.head args) ss
    let Pred' ← Meta.inferType (mkWP concreteProg abstractProg)
    withLocalDeclD `Pre Pred' fun pre => do
    let sampleGoal ← mkAppM ``PartialOrder.rel #[pre, mkWP concreteProg abstractProg]
    let relArgs := sampleGoal.getAppArgs
    let relHead := mkAppN sampleGoal.getAppFn (relArgs.extract 0 3)
    let mkGoal (prog abs : Expr) : Expr := mkApp relHead (mkWP prog abs)
    -- Use synthetic opaque mvars so that `rwIfOrMatcher`'s `assumption` cannot
    -- accidentally assign our subgoal metavariables.
    let subgoals ← splitInfo.altInfos.mapM fun _ =>
      mkFreshExprSyntheticOpaqueMVar (mkSort 0)
    let namedSubgoals := subgoals.mapIdx fun i mv => ((`h).appendIndexAfter (i+1), mv)
    withLocalDeclsDND namedSubgoals fun subgoalHyps => do
    let prf ←
      abstractInfo.splitWith
        (useSplitter := true)
        (mkGoal concreteProg abstractProg)
        (fun _name bodyType idx altFVars => do
          -- Extract the programs from `bodyType` (the substituted alt goal type).
          -- For matchers, `bodyType` has the discriminant replaced by the constructor
          -- pattern (e.g., `Nat.zero` instead of `discr`), which is required for
          -- `rwMatcher` to discharge the equality hypotheses of congr equation theorems.
          -- For ite/dite, `bodyType` equals `mkGoal concreteProg abstractProg`.
          let rhs := bodyType.getArg! 3
          let prog := rhs.getArg! WRPApp.progIdx
          let abs := rhs.getArg! (WRPApp.progIdx + 1)
          let res ← rwIfOrMatcher idx prog
          if res.proof?.isNone then
            throwError "mkBackwardRuleForSplit: rwIfOrMatcher failed for alt {idx}"
          let resA ← if absFVars.isEmpty then pure { expr := abs } else rwIfOrMatcher idx abs
          if !absFVars.isEmpty && resA.proof?.isNone then
            throwError "mkBackwardRuleForSplit: rwIfOrMatcher failed for the abstract alt {idx}"
          let altParams := altFVars.all
          subgoals[idx]!.mvarId!.assign (← mkForallFVars altParams (mkGoal res.expr resA.expr))
          let context ← withLocalDecl `x .default ma fun x =>
            mkLambdaFVars #[x] (mkGoal x abs)
          let mut eqProof ← mkAppM ``congrArg #[context, res.proof?.get!]
          if let some pa := resA.proof? then
            let contextA ← withLocalDecl `y .default info.args[1]! fun y =>
              mkLambdaFVars #[y] (mkGoal res.expr y)
            eqProof ← mkEqTrans eqProof (← mkAppM ``congrArg #[contextA, pa])
          mkEqMPR eqProof (mkAppN subgoalHyps[idx]! altParams))
    let prf ← instantiateMVars prf
    mkLambdaFVars (splitFVars ++ absFVars ++ ss ++ #[post, eposts, pre] ++ subgoalHyps) prf
  let prf ← instantiateMVars prf
  let res ← abstractMVars prf
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

end Lean.Elab.Tactic.VCGen.Distill
