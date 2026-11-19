# Benchmarks for the `distill` tactic

Each case states a `Refinement` with a `?_` hole for the abstract program. A solver fills the hole
and proves the triple. The driver `lib/Driver.lean` measures each phase of the run separately.

## Running

`lake build` runs every family. To run one family, use `lake env lean <file>`, for example
`lake env lean distill_add_sub_cancel.lean`. Run each command in the capped scope of `CLAUDE.md`:

```
systemd-run --user --scope -p MemorySwapMax=0 -p CPUWeight=50 --quiet timeout 120 lake env lean distill_add_sub_cancel.lean
```

The package has two run libraries. `Bench` holds the files `distill_*.lean`, whose cases are in
`cases/Cases/`. `BenchX64` holds the files `x64_*.lean`, whose cases are in `casesx64/CasesX64/`.
The x64 cases import the demo, so the package requires the demo package `../demo`.

## Output

The driver prints one line for each size:

```
AddSubCancel(30):      unfold 3 ms, solve 150 ms, 0 VCs, finish 0 ms, golden 3 ms, instantiate 2 ms, share 9 ms, kernel 9 ms, total 197 ms
```

| Field | Meaning |
|---|---|
| `unfold` | `Sym.simp` with the equations of the concrete program, before the solver |
| `solve` | the solver, usually `distill` |
| `VCs` | the number of verification conditions that the solver returns |
| `finish` | the discharge tactic on all verification conditions |
| `golden` | `isDefEq` of the synthesized program and the expected program, if the case gives one |
| `sym_simp_def` | the simplification of `sym_simp_def` on the synthesized program, if the case gives its rules |
| `instantiate` | `instantiateMVars` of the synthesized program and of the proof |
| `share` | `ShareCommon.shareCommon` of the proof |
| `kernel` | the kernel check of the shared proof |
| `total` | the wall time of the whole size, elaboration of the statement included |

## Families

The sizes of each family have the ratio 1:2:3. The time is the minimum over three runs of the sum
of `total` over the three sizes.

### Mirrors of the `vcgen` bench

Each family runs the program of a case of core's bench `tests/bench/vcgen` over a monad on
`Distillery.Demonic`, under `Concretization.id`. The abstract program is the concrete program,
which the golden check confirms. In `DiteSplit` and `MatchSplit` the abstract program splits on the
abstract read value, and the abstract `if` decides its condition by `Classical.propDecidable`, so
these two families have no golden check.

| Family | File | Monad | Sizes | Time | `vcgen` sizes |
|---|---|---|---|---|---|
| `AddSubCancel` | `distill_add_sub_cancel.lean` | `StateT Nat Demonic` | 30, 60, 90 | 1.31 s | 200, 1200, 2200 |
| `AddSubCancelSimp` | `distill_add_sub_cancel_simp.lean` | `StateT Nat Demonic` | 30, 60, 90 | 1.24 s | 100, 400, 700 |
| `AddSubCancelDeep` | `distill_add_sub_cancel_deep.lean` | three `ExceptT`, `ReaderT`, two `StateT` | 30, 60, 90 | 1.48 s | 100, 500, 900 |
| `GetThrowSet` | `distill_get_throw_set.lean` | `ExceptT String (StateT Nat Demonic)` | 30, 60, 90 | 1.13 s | 200, 500, 800 |
| `MatchIota` | `distill_match_iota.lean` | `ExceptT String (StateT Nat Demonic)` | 20, 40, 60 | 1.12 s | 500, 1000, 1500 |
| `PurePrecond` | `distill_pure_precond.lean` | `StateT Bool Demonic` | 150, 300, 450 | 1.33 s | 400, 2400, 4400 |
| `ReaderState` | `distill_reader_state.lean` | `ReaderT Nat (StateT Nat Demonic)` | 20, 40, 60 | 1.22 s | 600, 1600, 2600 |
| `RegFile` | `distill_reg_file.lean` | `StateT Regs Demonic` | 30, 60, 90 | 1.32 s | 128, 256, 384 |
| `AdcChain` | `distill_adc_chain.lean` | `StateT S Demonic` | 150, 300, 450 | 1.25 s | 250, 500, 750 |
| `DiteSplit` | `distill_dite_split.lean` | `ExceptT String (StateT Nat Demonic)` | 20, 40, 60 | 1.88 s | 500, 1000, 1500 |
| `MatchSplit` | `distill_match_split.lean` | `ExceptT String (StateT Nat Demonic)` | 60, 120, 180 | 0.94 s | 500, 1000, 1500 |
| `LetBinding` | `distill_let_binding.lean` | `StateT Nat Demonic` | 20, 40, 60 | 0.96 s | 10 |
| `IfsJP` | `distill_ifs_jp.lean` | `StateT Nat Demonic` | 5, 10, 15 | 1.08 s | 3 (`+jp`) |
| `MatchesJP` | `distill_matches_jp.lean` | `StateT Nat Demonic` | 4, 8, 12 | 1.39 s | 3 (`+jp`) |
| `WideJP` | `distill_wide_jp.lean` | `StateT Nat Demonic` | 30, 60, 90 | 1.22 s | 4 (`+jp`) |

`IfsJP`, `MatchesJP` and `WideJP` give the abstract program one join point for each concrete join
point, so the run distills the code after each split once. `WideJP` weakens the postcondition of the split
of `chain n x`, so that the `n + 1` results share one abstract continuation. In `WideJP`, `share` grows faster than quadratically: 22, 86 and 355 ms. In `DiteSplit`,
`instantiate` grows quadratically: 15, 121 and 590 ms.

`GetThrowSet` throws by `throwIf`, whose rule abstracts the condition. `AddSubCancelDeep` puts
every `ExceptT` above the `ReaderT` and the two `StateT`, the order for which `EPostsConcretization`
has an instance.

### Families of `distill`

| Family | File | Program | Sizes | Time |
|---|---|---|---|---|
| `Loop` | `distill_loop.lean` | one `FixLoop` loop, body of `n` writes, invariant in `invariants` | 240, 480, 720 | 0.97 s |
| `Table` | `distill_table.lean` | a table of `n` cells with jumps, through `wrp_cells` | 30, 60, 90 | 1.12 s |
| `Catch` | `distill_catch.lean` | `n` nested `tryCatch` around a `throw` | 250, 500, 750 | 1.07 s |
| `Holes` | `distill_holes.lean` | `n` binds and the sum of the `n` bound values | 25, 50, 75 | 0.88 s |
| `Entries` | `distill_entries.lean` | `n` register entries in the precondition, the sum read at the end | 30, 60, 90 | 0.97 s |
| `Backtrack` | `distill_backtrack.lean` | `k` failing candidate specs before the rule that applies | 60, 120, 180 | 1.19 s |
| `WordAbs` | `distill_word_abs.lean` | the guarded word chain, by a generated proof term | 120, 240, 360 | 1.37 s |
| `WordAbsVal` | `distill_word_abs_val.lean` | the guarded word chain, by `@[distill_pure]` rules | 120, 240, 360 | 1.38 s |
| `WordAbsValR` | `distill_word_abs_val.lean` | the right-nested guarded word chain | 120, 240, 360 | 1.43 s |

The `WordAbs` solver builds the rule-chain proof directly, without search and without a rule
database. It is the reference for the engine families of the guarded word chain.

### x64 families on the kraken stub

Each family refines an x64 text over the stub `demo/Demo/Kraken/` to the block loop of the
abstract machine by `refines_cfg`. Then the driver runs the `sym_simp_def` step with the rules of
the straight-line stack frame tests of the demo.

| Family | File | Program | Sizes | Time |
|---|---|---|---|---|
| `X64Straight` | `x64_straight.lean` | `n` pairs of `addq` and `movq` | 35, 70, 105 | 1.19 s |
| `X64Calls` | `x64_calls.lean` | `n` calls to `_swap` | 150, 300, 450 | 1.65 s |
| `X64Frame` | `x64_frame.lean` | `n` pushes, then `n` pops | 15, 30, 45 | 0.99 s |
| `X64Array` | `x64_array.lean` | `n` loads and `n` stores at distinct indices | 15, 30, 45 | 0.93 s |

## Calibration

One run of a family, all three sizes, takes at most 2 s of wall time on an idle machine. The
machine is shared, so the calibration measures under load:

1. Run the file of the family three times, one run after the other, in the capped scope.
2. For each run, add the `total` of the three sizes.
3. Take the minimum of the three sums.
4. If the minimum is above 2 s, decrease the sizes and keep the ratio 1:2:3.

The times in the tables above are from 2026-11-18, at a load average of 12 to 16 on 96 cores. The
times of `LetBinding`, `IfsJP`, `MatchesJP`, `WideJP` and `DiteSplit` are from 2026-11-19, at a load average of 35 to 150.
