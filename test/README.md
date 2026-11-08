# Tests

Run the suite with

```
lake build AscentTests
```

The library `AscentTests` builds every test module with `sym.debug` on. A failing `#guard_msgs`
or a failing `ascend` run is a build error.

## Rule

Every fixed bug of the `ascend` engine or of the refinement framework gets a minimal test in
`AscentTests/Regress`, and every deviation of `patches/vcgen/series` has at least one test whose
outcome depends on it. A test uses the smallest setup that shows the behaviour, imports no kraken,
and names the bug or deviation in its module doc.

## Setup

`AscentTests/Setup/Blocks.lean` is a toy block machine: the concrete state has a register `r` and
a zero flag `zf`, the abstract state is the register alone, a block program runs in
`BlockM σ := ExceptT Lbl (StateT σ UB)`, and a table of cells runs through `cells`. Its
`@[ascend]` rules cover a decrement that writes the flag, a jump on the flag, a register write,
and the table of cells, so a test reaches value carrying, continuation holes and table slots with a
few lines.

## Deviation coverage

Each deviation of `patches/vcgen/series` (see `docs/vcgen-fork.md`) and the tests whose outcome
depends on it. "Verified" means: with the deviation removed, or its code site disabled, the listed
tests fail.

| Deviation | What it does | Tests | Verified |
|---|---|---|---|
| D7 | no frame rules in the forked modules | every `ascend` test | no: without D7 the forked `RuleConstruction` does not compile |
| D8 | spec rules take the concrete side verbatim and stay schematic in the abstract side | every test that applies `wrp_bind` at an `ExceptT` stack with a hole, e.g. `Regress/BinderHole`, `Regress/HoleScope` | no: without D8 the later patches do not apply |
| D6, bare and delayed holes | a hole applied to distinct variables is filled by delayed assignment | `Regress/BinderHole`, `Regress/HoleScope`, `Regress/Lockstep`, `PureRefinement`, `WordAbsEngine` | yes, by disabling the delayed case |
| D6, closed arguments | a hole applied to closed terms is filled by a constant function | `Regress/Commands`, `Regress/HoleScope`, `Regress/Lockstep` | yes, by disabling the closed case |
| D6, table slots | a slot `Table.get ?tbl k` is filled by the cell of `k` | `Regress/HoleScope` | yes, by disabling the table case |
| D6, hole scope | holes left by a rule take the context of the filled hole | `Regress/HoleScope` | yes, by disabling `restoreHoleScope` |
| D2 | `wp` goals of the worklist go to core `solve` | `ForkTracer`, `Corpus/ZipL1L2` | yes, by disabling the dispatch |
| D11 | a `Refinement` spec keeps its abstract program schematic | `AscendUnfold`, `PureRefinement`, `Regress/HoleScope` | yes, by removing the patch |
| D12, pure refinements | `PureRefinement` goals go to their solver | `PureRefinement`, `WordAbsEngine`, `Regress/Lockstep`, `Regress/HoleScope` | yes, by disabling the dispatch |
| D12, two-sided split | an `if` splits both programs on one condition | `Regress/IteSplit` | no: without D12 the forked `Solve` does not compile |

## Regressions

| Test | Origin |
|---|---|
| `Regress/HoleScope` | `efc5cac`: "unknown free variable" when a table cell keeps a hole under a carried flag |
| `Regress/BinderHole` | continuation holes applied to a bound value (the demo's `LiftTest`) |
| `Regress/IteSplit` | `a14ae3e`: the split of an `if` put the abstract program in the concrete slot |
| `Regress/Lockstep` | `113749a`: the loop value stayed unassigned under a named step relation; the `match` post reduces |
| `Regress/Commands` | `a14ae3e`, `62af746`: "declaration has metavariables" from a binder of type `Array Nat`; `0581e81` names in the current namespace; `423b076` used binders; `99e069f` refinement notation |
| every `wrp_bind` test on `BlockM` | `0ee3ec1`: a generic rule failed on an `ExceptT` stack because the matcher met `?AM ?AV` |
| `FixLoopDelab` | `68f7877` and the `repeat'` delaborator round trip |

Past problems that a test here does not pin:
- The kernel unfolds `Bind.bind` chains when a rule premise applies a pattern variable under `>>=`
  (2026-11-04, quadratic kernel time). A performance cliff, measured by the bench case
  `Cases/WordAbsVal` (a left-nested chain that `wrp_bind_assoc` and `wrp_kleisli` reassociate).
- `instantiateNewMVarTypes` of Sym is quadratic on left-nested chains (lean4#16241). A performance
  cliff in core; no test or bench case pins it here.
- Open: vcgen gives no option to raise the step limit of its `Sym.simp` step (100,000 per call).
- Open: a top-level concrete step whose goal spells the abstract type as the abbreviation
  `BlockM σ` finds no rule; under a bind it does.
- Open: a hole applied to a closed term and a variable together, such as `?fa () a`, is not filled;
  `Regress/Lockstep` states its loop rule with `fa : βa → …` for this reason.
- Open: the generic `wrp_pure` applies before `wrp_yield` when both are registered, and then the
  loop value stays a hole.
- `List.mem_cons` in `vcgen_simp` rewrites the binder domain of `∀ x ∈ a :: l` and stops the
  `forall_mem_cons_intro` split. A configuration pitfall, not an engine bug.
