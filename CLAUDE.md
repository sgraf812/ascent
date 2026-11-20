# Working on Distillery

Distillery is a Lean library for refinement between programs, with the tactic `distill` and the
command `distill_def` that synthesize an abstract program from a concrete one. `README.md` explains
the judgment and the modules. This file explains how to develop the repository.

## Build

Run every build in a capped scope, so that a runaway elaboration cannot take the machine down:

```
systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout <s> lake build
```

| Target | Command, in the scope above |
|---|---|
| library | `lake build` |
| tests | `lake build DistilleryTests` |
| bench | `lake build` in `bench/` |
| demo | `lake build` in `demo/` |

Before a commit, all four targets build and `scripts/sync-vcgen.py --check` passes. The demo builds
without external projects, so it belongs to every check, also to the ablation of the patch series.

`lean-toolchain` pins the toolchain. Do not change it without an explicit request. The demo builds
on `demo/Demo/Kraken/`, a stub of kraken's API. It has kraken's definitions where their bodies use
only what the stub has, opaque constants for the other operations, and axioms that state kraken's
theorems. A new use of kraken's API adds kraken's definition when its body fits the stub. A property
that the demo needs of an opaque constant is an axiom with kraken's statement.

## Tests

`test/README.md` states the rule. In short:

- Every fixed bug of the engine or of the framework gets a minimal test in
  `test/DistilleryTests/Regress`, on the toy machine `DistilleryTests.Setup.Blocks`, without kraken.
  Its module doc names the bug.
- Every test states its purpose in its module doc. A test that guards a deviation of the patch
  series names that deviation, and `docs/vcgen-fork.md` names one such test for each deviation.
- The tests build with `sym.debug` on.
- A feature that only the demo exercises gets a test here first.

## The engine and its patch series

`Distillery/Tactic/VCGen/` has two kinds of modules:

- **Translated modules** (`Driver`, `JoinPoint`, `RuleCache`, `RuleConstruction`, `Solve`):
  `scripts/sync-vcgen.py` derives them from the `vcgen` sources of the toolchain by the translation
  table of `docs/vcgen-fork.md`, then applies `patches/vcgen/series`. Every other change in these
  modules is a deviation.
- **Hand-written modules** (`Command`, `Frontend`, `PureRefinement`, `Shim`, `WRPApp`): ordinary
  code, outside the series.

To change a translated module:

1. Edit the module, build, and run the tests.
2. If the change belongs to an existing deviation, run `scripts/refresh-patch.py <patch>` to
   rewrite that patch from the tree.
3. If it is a new deviation, add a patch to `patches/vcgen/` and a line to `series`, a section to
   `docs/vcgen-fork.md` with intent, change and acceptance, and a test whose module doc names the
   deviation.
4. Run `scripts/sync-vcgen.py --check`. It fails when the translation and the series do not
   reproduce the committed tree.

`scripts/sync-vcgen.py` with no argument regenerates the tree in place, and `--raw <dir>` writes the
translation without the patches.

### Ablation

The series contains only deviations that a test or a compile dependency needs. To check this after
a toolchain update or a large change:

1. Split the difference between the raw translation and the tree into single-change units.
2. Revert each unit alone to the raw translation, and run the library, the tests and the demo.
3. For the units that do not compile alone, revert the units of one feature together.
4. Drop every unit or group whose reversion passes everything and does not slow the bench. A unit
   that only the demo needs stays, and gets a regression test in `test/DistilleryTests/Regress`.
5. Regenerate the patches as the differences between consecutive trees, one deviation at a time,
   and update the acceptance lines in `docs/vcgen-fork.md`.

Run the reversions in parallel worktrees, each with its own `.lake`.

### Toolchain updates

`docs/vcgen-fork.md` describes the procedure in its section "Maintenance".

## Bench

Run each bench case under a short timeout. A case that takes more than 10 s at `n = 2000` is a
failure, not a measurement. The wall times vary by a factor of 2 between runs under load, and the
instruction counts by less than 1 %, so compare instructions. `scripts/bench-record.py` records
them in `bench/results.csv` and compares two commits (`bench/README.md`, section "Recording").

## Conventions

- Prose in comments, docstrings and documents follows the rules of Simplified Technical English:
  short sentences, one instruction each, active voice, no hedges. Describe what exists, without
  contrast to rejected alternatives, and without references to pull requests or issues.
- No docstrings on theorems. Name no instances.
- Reuse library lemmas and combinators before a new definition. Prove against the simp and `grind`
  lemmas of a definition, not by unfolding it.
- In `SymM` code, build goal and proposition terms with the `SymM` builders (`mkAppNS`,
  `mkConstS`, `shareCommon`, …), never with `Meta.mkAppM` and similar.
- Avoid `decide`, except `decide +kernel`.
