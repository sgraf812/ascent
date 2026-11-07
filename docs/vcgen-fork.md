# The ascend fork of vcgen

`ascend` is a fork of `vcgen` (`Lean.Elab.Tactic.VCGen` and the spec attribute in
`Lean.Elab.Tactic.Do.Attr`). `vcgen` decomposes goals `pre ⊑ wp x Q E s⃗`. `ascend` decomposes
goals `pre ⊑ wrp γ c a Q E s⃗`, where `a` contains the synthesis hole of the abstract program.
The fork consists of three parts:

1. modules of `vcgen` that `ascend` imports and calls unchanged,
2. modules that a fixed translation table derives from `vcgen` (`T1` to `T4` below),
3. a list of deviations, one patch each, in the order of `patches/vcgen/series`.

Every change to `vcgen` code that is not in the translation table is a deviation, and this
document lists it with its intent, the place it changes, and its acceptance test.

## Example

The concrete program is `setSize "n" m >>= fun _ => getSize "n"` and the concretization is
`ofStateRepr (·.heap)`. The run has one worklist with two kinds of goals:

```
P s ⊑ wrp γ (setSize "n" m >>= fun _ => getSize "n") ?a Q E s       -- ascend goal
  stutter spec:
P s ⊑ wp (setSize "n" m) (fun _ s' => ⌜s'.heap = s.heap⌝ ⊓ wrp γ (getSize "n") ?a Q E s') ⊥ s
                                                                      -- vcgen goal
  setSize_spec, state simp:   s₁ := { s with locals := … }, ⌜s₁.heap = s.heap⌝ ↝ True
P' ⊑ wrp γ (getSize "n") ?a Q E s₁                                    -- ascend goal
  read spec:                  ?a := pure ?av
  getSize_spec, match iota:   Q m ?av s₁
  VC cleanup:                 ?av := m
```

The `vcgen` goals go to `vcgen`'s own `solve`. The `ascend` goals go to the forked `solve`. The
value of the local `"n"` comes from the state term `s₁`, and the abstract value comes from
unification.

## Layout

| Path | Content |
|---|---|
| `Ascent/Tactic/VCGen/` | the translated modules, one file for each `vcgen` file it derives from |
| `Ascent/Tactic/Shim.lean` | the `wrp` lemmas that `T4` substitutes, with the binder order of their `wp` counterparts |
| `patches/vcgen/series` | the order of the deviation patches |
| `patches/vcgen/D<n>-<name>.patch` | one patch for each deviation |
| `scripts/sync-vcgen` | regenerates `Ascent/Tactic/VCGen/` from the toolchain in `lean-toolchain` |

`scripts/sync-vcgen` copies the source files from the pinned toolchain, applies `T1` to `T4`, and
then applies the patches in `series`. CI runs the script and fails if its output differs from
the committed `Ascent/Tactic/VCGen/`. So `diff` between the toolchain source and the committed
tree shows exactly the translation and the deviations.

## Imported unchanged

`ascend` runs in `VCGenM` with an additional state layer:
`AscendM := StateRefT AscendState VCGenM`. These modules are imported, and their functions are
called through `liftM`:

- `Context`, `Util`, `Reduce`, `BinderName`, `LatticeOp`, `Entails`: phases 1 to 3 of `solve`,
  `introsExcessArgs`, `simpGoalTelescope`, `cleanupVC`.
- `Solve`, `SpecDB`, `RuleConstruction`, `RuleCache`, `FrameProc`: the `vcgen` goals of the
  worklist.
- The `@[spec_invariant_type]` attribute: invariant holes of loop specs.

## Translation table

`T1`. Namespaces and names. `Lean.Elab.Tactic.VCGen` becomes `Ascent.Tactic.VCGen`.
`Lean.Elab.Tactic.Do.SpecAttr` becomes `Ascent.Tactic.SpecAttr`. The attribute `spec` becomes
`ascend`.

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

| `vcgen` | `ascend` |
|---|---|
| `Std.WP.Triple.intro` | `Ascent.Refinement.intro` |
| `WP.wp_monotone_post_le` | `Ascent.wrp_mono_post_le` |
| `WP.wp_monotone_epost_le` | `Ascent.wrp_mono_erel_le` |
| `WP.wp_monotone_bot_le` | `Ascent.wrp_mono_bot_le` |
| `Std.WP.wp_le_wp_of_eq` | `Ascent.wrp_le_wrp_of_eq` |
| `tripleToWpProof?` | `refinementToWrpProof?` |

The translated modules are `WPApp`, the phase 4 steps of `Solve` (`wpLet?`, `wpSimpStateArgs?`,
`wpMatch?`, `wpFVarZeta?`, `wpHeadReduce?`, `applySpec`, `applySpecs`), `SpecDB`, the spec rule
construction of `RuleConstruction` (`mkSpecBackwardProof`, `tryMkBackwardRuleFromSpec`,
`mkBackwardRuleForSplit`), `RuleCache`, `Driver`, `Frontend`, and the spec attribute of
`Do/Attr.lean`.

## Deviations

The series applies `D7`, `D8`, `D6`, `D2`, `D11` and `D12`, in this order, to the sources of the
toolchain in `lean-toolchain`.

### D7. No frame rules

**Intent.** An `ascend` goal has no frame operator, so the forked modules carry no frame
machinery.

**Change.** `RuleConstruction`, `RuleCache` and `Solve` lose `mkFrameBackwardRule`, its cache, the
`frames` alternatives and the frame callbacks. `applySpec` applies the spec rule directly.

**Acceptance.** Every `ascend` test in `test/AscentTests` runs without a frame rule.

### D8. Rule construction for `wrp` specs

**Intent.** A spec rule takes the concrete side of the goal verbatim, as core does, and is
schematic in the abstract side, so one compiled rule serves every abstract program.

**Change.** `tryMkBackwardRuleFromSpec` unifies the abstract types and `γ` of the spec with the
goal's prefix, then the concrete `WP` instance, then synthesizes the instance binders whose types
are closed. The abstract value type, `WP` instance and program become rule parameters. The rule
caches key on the hash-consed `wrp` prefix.

**Acceptance.** `ZipWithAdd` and `WordAbsEngine` apply generic rules such as `wrp_bind` at block
stacks with several abstract monads.

### D6. Synthesis holes in their context

**Intent.** The run fills a hole of the abstract program only with terms in the hole's context.

**Change.** `applySpec` fills an unassigned hole through a fresh metavariable of the goal's
context: a bare hole directly, a hole applied to distinct free variables by delayed assignment, a
hole applied to closed terms by a constant function, and a `Table.get ?tbl k` slot at a closed key
by the cell of `k`.

**Acceptance.** `AscendDef` and the demo's `zipWithAddA` synthesize a block table.

### D2. One worklist for `wrp` and `wp` goals, and holes as data

**Intent.** A concrete step without an abstract counterpart is decomposed by `vcgen`'s own rules
and `@[spec]` database, and a hole is never emitted as a verification condition.

**Change.** `work` sends a goal `pre ⊑ wp …` to `vcgen`'s `solve` with the core scope. A subgoal
whose type is not a proposition stays a natural metavariable.

**Acceptance.** `Pipeline` mixes `@[spec]` steps with `@[ascend]` rules.

### D11. Schematic abstract program in a refinement spec

**Intent.** A spec stated as a `Refinement` applies to a goal whose abstract program is a hole.

**Change.** The rule built from such a spec keeps its abstract program schematic, so the rule
does not capture the goal's hole.

**Acceptance.** `AscendUnfold`.

### D12. Pure refinements and the two-sided split

**Intent.** A value of the concrete program is refined to an abstract value by the
`PureRefinement` solver, and a concrete `if` splits both programs on the same condition.

**Change.** The driver dispatches `PureRefinement` goals to the solver of
`Ascent/Tactic/VCGen/PureRefinement.lean`. `mkBackwardRuleForSplit` splits an `ite`, `dite` or
`cond` on both sides with one fresh abstract branch per alternative, after `fillAbstractHole`
fills the abstract hole. A matcher still splits on the concrete side only.

**Acceptance.** `PureRefinement`, `WordAbsEngine`, and the register and array layers of the demo.

### Covered by core

Core vcgen covers these earlier deviations, which the series no longer contains: the product
binder split and the list membership split, through `@[vcgen_rintro]` rules (`Prod.forall_intro`,
and `forall_mem_cons_intro`/`forall_mem_nil_intro` in `Ascent/Table.lean`), and the head
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
