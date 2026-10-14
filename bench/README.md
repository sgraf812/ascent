# Benchmarks for the `ascend` tactic

Synthesis benchmarks: each case elaborates a `Refinement` statement with a `?_` hole for the
abstract program, hands it to a solver that instantiates the hole while proving the triple, and
measures solve time, VC discharge, the golden `isDefEq` check of the synthesized program against
its expected image, and kernel-checking time, each separately.

To run all benchmarks, `lake build`. To run one, `lake lean ascend_word_abs.lean`.

The `Baseline` solvers build the rule-chain proof directly (no search, no rule database); they
are the speed-of-light reference the ascend engine is measured against.
