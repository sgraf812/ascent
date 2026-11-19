# The distill fork of vcgen

`distill` is a fork of `vcgen` (`Lean.Elab.Tactic.VCGen` and the spec attribute in
`Lean.Elab.Tactic.Do.Attr`). `vcgen` decomposes goals `pre ⊑ wp x Q E s⃗`. `distill` decomposes
goals `pre ⊑ wrp γ c a Q E s⃗`, where `a` contains the synthesis hole of the abstract program.
The fork consists of three parts:

1. modules of `vcgen` that `distill` imports and calls unchanged,
2. modules that a fixed translation table derives from `vcgen` (`T1` to `T4` below),
3. a list of deviations, one patch each, in the order of `patches/vcgen/series`.

Every change to `vcgen` code that is not in the translation table is a deviation, and this
document lists it with its intent, the place it changes, and its acceptance test.

## Example

The concrete program is `setSize "n" m >>= fun _ => getSize "n"` and the concretization is
`ofStateRepr (·.heap)`. The run has one worklist with two kinds of goals:

```
P s ⊑ wrp γ (setSize "n" m >>= fun _ => getSize "n") ?a Q E s       -- distill goal
  stutter spec:
P s ⊑ wp (setSize "n" m) (fun _ s' => ⌜s'.heap = s.heap⌝ ⊓ wrp γ (getSize "n") ?a Q E s') ⊥ s
                                                                      -- vcgen goal
  setSize_spec, state simp:   s₁ := { s with locals := … }, ⌜s₁.heap = s.heap⌝ ↝ True
P' ⊑ wrp γ (getSize "n") ?a Q E s₁                                    -- distill goal
  read spec:                  ?a := pure ?av
  getSize_spec, match iota:   Q m ?av s₁
  VC cleanup:                 ?av := m
```

The `vcgen` goals go to `vcgen`'s own `solve`. The `distill` goals go to the forked `solve`. The
value of the local `"n"` comes from the state term `s₁`, and the abstract value comes from
unification.

## Layout

| Path | Content |
|---|---|
| `Distillery/Tactic/VCGen/` | the translated modules, one file for each `vcgen` file it derives from |
| `Distillery/Tactic/Shim.lean` | the `wrp` lemmas that `T4` substitutes, with the binder order of their `wp` counterparts |
| `patches/vcgen/series` | the order of the deviation patches |
| `patches/vcgen/D<n>-<name>.patch` | one patch for each deviation |
| `scripts/sync-vcgen` | regenerates `Distillery/Tactic/VCGen/` from the toolchain in `lean-toolchain` |

`scripts/sync-vcgen` copies the source files from the pinned toolchain, applies `T1` to `T4`, and
then applies the patches in `series`. CI runs the script and fails if its output differs from
the committed `Distillery/Tactic/VCGen/`. So `diff` between the toolchain source and the committed
tree shows exactly the translation and the deviations.

## Imported unchanged

`distill` runs in `VCGenM` with an additional state layer:
`DistillM := StateRefT DistillState VCGenM`. These modules are imported, and their functions are
called through `liftM`:

- `Context`, `Util`, `Reduce`, `BinderName`, `LatticeOp`, `Entails`: phases 1 to 3 of `solve`,
  `introsExcessArgs`, `simpGoalTelescope`, `cleanupVC`.
- `Solve`, `SpecDB`, `RuleConstruction`, `RuleCache`, `FrameProc`: the `vcgen` goals of the
  worklist.
- The `@[spec_invariant_type]` attribute: invariant holes of loop specs.

## Translation table

`T1`. Namespaces and names. `Lean.Elab.Tactic.VCGen` becomes `Distillery.Tactic.VCGen`.
`Lean.Elab.Tactic.Do.SpecAttr` becomes `Distillery.Tactic.SpecAttr`. The attribute `spec` becomes
`distill`.

`T2`. Module headers. `module`, `prelude` and `public section` are removed. `public import`
becomes `import`. `builtin_initialize` becomes `initialize`.

`T3`. Goal metadata. `WPApp` becomes `WRPApp`, and `isWPApp?` becomes `isWRPApp?`, which
recognizes `wrp` with its 21 arguments followed by the excess state arguments. The accessors
map as follows:

| `WPApp` | `WRPApp` |
|---|---|
| `prog` | `c` (the abstract program is `a`) |
| `post` | `Q` |
| `eposts` | `E` |
| `Pred` | `CPred` |
| `M` | `CM` |
| `instWP` | `instWPc` |

`T4`. Lemmas. Each lemma in the left column becomes the `Shim.lean` lemma in the right column:

| `vcgen` | `distill` |
|---|---|
| `Std.WP.Triple.intro` | `Distillery.Refinement.intro` |
| `WP.wp_monotone_post_le` | `Distillery.wrp_mono_post_le` |
| `WP.wp_monotone_epost_le` | `Distillery.wrp_mono_erel_le` |
| `WP.wp_monotone_bot_le` | `Distillery.wrp_mono_bot_le` |
| `Std.WP.wp_le_wp_of_eq` | `Distillery.wrp_le_wrp_of_eq` |
| `tripleToWpProof?` | `refinementToWrpProof?` |

The translated modules are `WPApp`, the phase 4 steps of `Solve` (`wpLet?`, `wpSimpStateArgs?`,
`wpMatch?`, `wpFVarZeta?`, `wpHeadReduce?`, `applySpec`, `applySpecs`), `SpecDB`, the spec rule
construction of `RuleConstruction` (`mkSpecBackwardProof`, `tryMkBackwardRuleFromSpec`,
`mkBackwardRuleForSplit`), `RuleCache`, `Driver`, `Frontend`, and the spec attribute of
`Do/Attr.lean`.

## Deviations

The series applies `D1` to `D9`, in this order, to the sources of the toolchain in
`lean-toolchain`. Each deviation is in the series because a test fails without it, or because
the code of a later deviation or of the frontend does not compile without it. The acceptance of a
deviation names that dependency or a test that fails without the deviation. The module doc of the
test names the deviation.

### D1. One worklist for `wrp` and `wp` goals

**Intent.** A concrete step without an abstract counterpart is decomposed by `vcgen`'s own rules
and `@[spec]` database.

**Change.** `work` sends a goal `pre ⊑ wp …` to `vcgen`'s `solve` with the core scope, which every
work item carries next to the `distill` scope. `run` takes both scopes.

**Acceptance.** The frontend passes both scopes to `run`. Test: `ForkTracer`.

### D2. No frame rules

**Intent.** A `distill` goal has no frame operator, so the forked modules carry no frame
machinery.

**Change.** `RuleConstruction`, `RuleCache` and `Solve` lose `mkFrameBackwardRule`, its cache, the
frame alternatives of `applySpecs`, the conjunctivity check of `applySpec`, and the `let` binders of
the frame callbacks.

**Acceptance.** The frame code does not type-check against `WRPApp`.

### D3. Rule construction for `wrp` specs

**Intent.** A spec rule takes the concrete side of the goal verbatim, as core does. The return
relation and the exception relation bind a concrete and an abstract value.

**Change.** `mkBackwardRuleFromSpec` binds the return relation over the abstract and the concrete
value, and takes the goal's concrete prefix verbatim. A fixed exception relation of the spec is
weakened to the goal's relation by `wrp_mono_erel_le`, which holds because `ePosts` of every
`EPostsConcretization` is monotone in the relation. `decomposeProdRel` builds one pointwise VC for
each component of the relation. It counts the exception arguments of a component from the number
of state arguments: a relation `εc → εa → σ → Prop` binds two, and a concrete-only layer
`εc → σ → Prop` binds one.

**Acceptance.** Test: `Regress/BareExceptionRelation`, whose spec does not apply when a fixed
exception relation is matched structurally.

### D4. Schematic abstract program in a refinement spec

**Intent.** A spec stated as a `Refinement` applies to a goal whose abstract program is a hole.

**Change.** The rule built from such a spec keeps its abstract program schematic, so the rule
does not capture the goal's hole.

**Acceptance.** Test: `Regress/RefinementPremise`.

### D5. Synthesis holes in their context

**Intent.** The run fills a hole of the abstract program only with terms in the hole's context.

**Change.** `applySpec` fills an unassigned hole through a fresh metavariable of the goal's
context: a bare hole directly, a hole applied to distinct free variables by delayed assignment, a
hole applied to closed terms by a constant function, and a `Table.get ?tbl k` slot at a closed key
by the cell of `k`. A hole whose spine mixes free variables, closed terms of a subsingleton type
and structure instances of free variables, such as `?f () a` or `?f (a, b)`, is solved through the
partial inverse of its spine (`patternHole?`), a fragment of nested pattern unification (Kovács and
Bocquet, WITS 2023): a pair `(a, b)` of free variables inverts to the projections `p.1`, `p.2` of
the bound argument, and a closed argument of a subsingleton type inverts to nothing by its η rule.
The result is a hole applied to the free variables, which takes the delayed assignment. The holes
that the rule leaves in the filled program take the context of the filled hole, and the cache of
`Sym.getMaxFVar?` starts afresh (`restoreHoleScope`). `applySpec` restores the state when the rule
fills a hole outside its scope. The hunk also defines `rhsExistsIntro?` and `mkWitnessHole`.

A `let` or `have` of a pure value distills into a `let` or `have` of the abstract value
(`wpHaveAbs?`). For `have x := e; b` and an abstract hole, the hole becomes
`have x' := ?e'; ?k x'`. The value solver closes `PureRefinement x ?e' True ?R` for the local
definition `x := e`, and the run continues on `b` and `?k x'` with the entry
`PureRefinement x x' True R`. The abstract type of `x'` and the relation `R` come from the rule that
abstracts `e`. For `let offset := v + 1; set (s + offset)`, the abstract program is
`have offset' := v + 1; set (x + offset')`. If no rule abstracts `e`, `wpLet?` introduces `x` alone,
and the solver abstracts each use of `x` through its value.

A join point `have jp := fun xs => k xs; body` of the do-elaborator distills into an abstract join
point (`wpJoinPoint?`). The abstract hole becomes `have jp' := ?k'; ?B jp'`. Each join parameter
`xᵢ` gets an abstract parameter `xᵢ'` with the entry `PureRefinement xᵢ xᵢ' True Rᵢ`, and a `PUnit`
parameter stays as it is. The goal for `body` receives `jp'` and the spec
`∀ xs ss x₁' h₁ … xₙ' hₙ, ?H xs ss → ⊤ ⊑ wrp γ (jp xs) (jp' xs') Q E ss`, and the goal for the
join RHS is the same entailment for `k xs` and `?k' xs'`. At a jump `jp vs` (`wpAbsJump?`), the value
solver abstracts each argument `vᵢ` to `vᵢ'`, the abstract program becomes `jp' vs'`, and the spec
closes the goal. `finalizeJoinPoint` assigns `?H` as for `vcgen +jp`, before the run reaches the
join RHS. So the run distills the join RHS once: for three consecutive `if`s that update a mutable
variable, the abstract program has three join points, six jumps and one `set`. The holes `?B`,
`?k` and `?k'` take the context of the filled hole extended by its arguments, so that a later split
recognizes the concrete state as outside of the hole.

A split copies its postcondition `Q` into each branch. For `(if c then pure 1 else pure 2) >>= k`,
the postcondition `fun cv av => wrp γ (k cv) (?a₂ av) Q' E` of the `if` contains the continuation,
and each branch would prove `k` again, at its own value. If `Q` contains a `wrp`, `wpWeakenPost?`
applies the rule of consequence before the split. The split gets the postcondition
`fun cv av ss => PureRefinement cv av True ?R ∧ ?H cv av ss`, with the goal
`(fun cv av ss => PureRefinement cv av True ?R ∧ ?H cv av ss) ⊑ Q`. Each leaf that reaches `?H`
is a jump (`wpPostJump?`), and `finalizeJoinPoint` assigns `?H` as for a join point. So the run
proves `Q` once, at variables `cv` and `av`, with the entry `PureRefinement cv av True R`. The rule
of consequence is cached for each `WP` instance and number of states, and the split rule stays the
same. A split that jumps to an abstract join point keeps `Q`, since the spec of the join point
states `Q`.

**Acceptance.** `D8` calls `rhsExistsIntro?`. Tests: `Regress/HoleScope`, `Regress/Have`,
`Regress/JoinPoint`, `Regress/Split`.

### D6. Pure refinements

**Intent.** A value of the concrete program is refined to an abstract value by the
`PureRefinement` solver of `Distillery/Tactic/VCGen/PureRefinement.lean`.

**Change.** The worklist solves a `PureRefinement` subgoal at once, so that the continuation sees
the abstract value and the precondition, and solves a `Refinement` subgoal with the specs of the
invocation. A verification condition that an entry of the solver's environment states is closed
by that entry.


**Acceptance.** `D9` uses the solver. Test: `Regress/GuardConsequence`.

### D7. Two-sided split

**Intent.** A concrete `if` or `match` splits both programs on the same condition or
discriminants.

**Change.** `mkBackwardRuleForSplit` splits an `ite`, `dite`, `cond` or matcher on both sides, after
`fillAbstractHole` fills the abstract hole. The abstract program is the same split over one fresh
abstract branch per alternative: for a matcher, the same matcher into the abstract program type,
over the pattern variables of each concrete alternative. A matcher that eliminates only into `Prop`
splits the concrete side only. Before the split, `wpAbstractCond?` abstracts a condition or a
discriminant that mentions a variable outside the context of the abstract hole, such as a value that
the run read from the concrete state: the value solver gives its abstract value `ad` with `d = ad`
under `Eq`, and the concrete program is rewritten to split on `ad` (`ite_congr`, `dite_congr`, or
`congrArg` for a matcher whose motive does not depend on its discriminants). The rewritten `ite`
and `dite` decide `ad` by `Classical.propDecidable`.

Before that, `wpMatchChain?` rewrites a matcher whose discriminant `d` mentions such a variable into
a chain of `dite`s, if the matcher has one discriminant, a motive that does not depend on it, no
equation name of it, closed patterns, and at most a final variable pattern. For a word `w`,
`match w with | 0 => A | 1 => B | x => C x` becomes
`if h : w = 0#8 then A else if h : w = 1#8 then B else C w`. Without a variable pattern, the last
alternative is the last `else`. `mkMatchChain` builds the chain and the proof of the rewrite once for
each matcher, from the equations of the matcher, over the parameters, the motive's type, the
discriminant and the alternatives. `wpAbstractCond?` then abstracts each condition `d = pᵢ` under
the relation of the value solver: for `w` with the number `n` under `WordNat`, `w = 0#8` becomes
`n = 0`, and the abstract program is the chain `if h : n = 0 then … else if h : n = 1 then … else …`.
After the split of a hole `?h xs`, the holes of the branches take the context of `?h` extended by
`xs`, so that the split of a later `dite` of the chain recognizes `w` as outside of the hole.

**Acceptance.** Test: `Regress/Split`.

### D8. Existential witness

**Intent.** An existential on the right side of an entailment is solved by synthesis.

**Change.** `solve` turns `pre ⊑ ∃ x, p x` on the `Prop` lattice into `pre ⊑ p ?x`, with `?x` a
fresh hole in the goal's context (`Distillery.le_exists_of_le`). For a tuple type the witness is
the tuple of fresh holes (`mkWitnessHole`), so that a `match` on it reduces.

**Acceptance.** Test: `Regress/ExistsHole`.

### D9. Spec backtracking on pure premises

**Intent.** A spec whose `PureRefinement` premise has no solution gives way to the next spec.

**Change.** `applySpecs` solves the `PureRefinement` premises of an applied candidate at once. When
the solver fails, it restores the state and tries the next candidate. When no candidate remains,
it raises the error of the last failed premise.

**Acceptance.** Test: `Regress/SpecBacktrack`.

### Covered by core

Core vcgen covers these earlier deviations, which the series no longer contains: the product
binder split and the list membership split, through `@[vcgen_rintro]` rules (`Prod.forall_intro`,
and `forall_mem_cons_intro`/`forall_mem_nil_intro` in `Distillery/Table.lean`), and the head
reduction of the entailment, through `instantiateGoal?`, which reduces assigned head
metavariables and `match` on constructors.

## Maintenance

On a toolchain update:

1. Update `lean-toolchain` and run `scripts/sync-vcgen`.
2. If a patch fails to apply, rewrite the patch from its intent in this document. Record
   whether the hunks applied exactly, applied with an offset, or needed a rewrite.
3. If a deviation is now in `vcgen`, delete its patch and its entry.
4. Run `lake build`, `lake test` and the bench. The bench must not regress.

A new deviation needs an entry in this document, a patch in `series`, and an acceptance test in
`test/`.
