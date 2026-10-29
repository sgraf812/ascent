# The ascend fork of vcgen

`ascend` is a fork of `vcgen` (`Lean.Elab.Tactic.VCGen` and the spec attribute in
`Lean.Elab.Tactic.Do.Attr`). `vcgen` decomposes goals `pre ⊑ wp x Q E s⃗`. `ascend` decomposes
goals `pre ⊑ wrp γ c a Q E s⃗`, where `a` contains the synthesis hole of the abstract program.
The fork consists of three parts:

1. modules of `vcgen` that `ascend` imports and calls unchanged,
2. modules that a fixed translation table derives from `vcgen` (`T1` to `T4` below),
3. a numbered list of deviations (`D1` to `D6` below), one patch each.

Every change to `vcgen` code that is not in the translation table is a deviation, and this
document lists it with its intent, the place it changes, and its acceptance test.

## Example

The concrete program is `setSize "n" m >>= fun _ => getSize "n"` and the concretization is
`ofStateRepr (·.heap)`. The run has one worklist with two kinds of goals:

```
P s ⊑ wrp γ (setSize "n" m >>= fun _ => getSize "n") ?a Q E s       -- ascend goal
  stutter spec (D3):
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

### D1. Synthesis holes

**Intent.** The run assigns the abstract hole of the goal and the data-typed parameters of the
rules it applies. It assigns no other metavariable.

**Change.** The frontend runs the worklist at the metavariable depth of the abstract hole. In
`work` and `emitVC`, a subgoal whose type is not a proposition stays a natural metavariable. The
driver neither emits it as a VC nor seals it.

**Acceptance.** The example above synthesizes `?a := pure m` with no VC.

### D2. One worklist for `wrp` and `wp` goals

**Intent.** A concrete step without an abstract counterpart is decomposed by `vcgen`'s own rules
and `@[spec]` database.

**Change.** The forked `solve` returns `← VCGen.solve scope goal` when the right-hand side of the
goal is a `wp` application. The `ascend` scope extends `vcgen`'s `Scope`, which carries the
`@[spec]` database, with the `@[ascend]` database.

**Acceptance.** The example above uses `setSize_spec` and `getSize_spec` unchanged.

### D3. Choice of the bind rule

**Intent.** On `c₁ >>= c₂`, the run applies the lockstep bind rule if `c₁` has an `@[ascend]`
spec, and the stutter rule otherwise.

**Change.** `applySpecs` on a bind looks up the `@[ascend]` specs of `c₁` before it selects the
bind rule.

**Acceptance.** A program that mixes a word operation with a `setSize` gives an abstract program
that contains only the word operation.

### D4. Two-sided split

**Intent.** A concrete `match x with alts` splits the abstract hole into
`match x' with alts'`, with one fresh hole for each alternative.

**Change.** `mkBackwardRuleForSplit` takes a goal builder `fun c => wrp γ c a Q E s⃗` in place of
the fixed argument positions. It builds the abstract matcher from the concrete `SplitInfo`.

**Acceptance.** `if` and `match` on a value that both programs share synthesize the abstract
`if` and `match`.

### D5. Exception relations in rule construction

**Intent.** A spec with a non-schematic exception relation yields one pointwise VC for each
layer of `ERels`.

**Change.** `decomposeProdRel` decomposes `ERels`, whose aligned layers are relations
`εc → εa → CPred`.

**Acceptance.** `ThrowCatch` and `TypeStrengthen` pass through the engine.

### D6. Rule cache key

**Intent.** A compiled rule is reused for every goal with the same spec, phase and number of
state arguments.

**Change.** The key is `(spec, ExprPtr γ, ExprPtr instWPc, excessArgs.size)` in place of
`(spec, ExprPtr instWP, excessArgs.size)`.

**Acceptance.** The `WordAbs` bench compiles each spec once for each phase.

## Maintenance

On a toolchain update:

1. Update `lean-toolchain` and run `scripts/sync-vcgen`.
2. If a patch fails to apply, rewrite the patch from its intent in this document. Record
   whether the hunks applied exactly, applied with an offset, or needed a rewrite.
3. If a deviation is now in `vcgen`, delete its patch and its entry.
4. Run `lake build`, `lake test` and the bench. The bench must not regress.

A new deviation needs an entry in this document, a patch in `series`, and an acceptance test in
`test/`.
