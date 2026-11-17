# Tests

Run the suite with

```
lake build DistilleryTests
```

The library `DistilleryTests` builds every test module with `sym.debug` on. A failing `#guard_msgs`
or a failing `distill` run is a build error.

## Rule

Every test states its purpose in its module doc: the behaviour it pins, and the bug or the
deviation of `patches/vcgen/series` that it guards. A test uses the smallest setup that shows the
behaviour and imports no kraken. Every fixed bug of the `distill` engine or of the refinement
framework gets such a test in `DistilleryTests/Regress`. Every deviation has at least one test,
which `docs/vcgen-fork.md` names.

## Setup

`DistilleryTests/Setup/Blocks.lean` is a toy block machine: the concrete state has a register `r` and
a zero flag `zf`, the abstract state is the register alone, a block program runs in
`BlockM σ := ExceptT Lbl (StateT σ Demonic)`, and a table of cells runs through `cells`. Its
`@[distill]` rules cover a decrement that writes the flag, a jump on the flag, a register write,
and the table of cells, so a test reaches value carrying, continuation holes and table slots with a
few lines.

## Tests in the demo

The kraken-free suite has no machine memory, so tests of stack accesses live in the demo, which
imports kraken. `demo/Demo/Tests/StackFrame.lean` pins the instruction-level synthesis and the structuring of leaf
functions that push and pop words and 16-bit values, reserve a local area with `sub rsp`, spill
words and bytes at unaligned offsets, and use the red zone below `rsp`. Build it with
`lake build Demo.Tests.StackFrame` in `demo/`.
