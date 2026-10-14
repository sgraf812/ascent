# Ascent

Ascent climbs from a concrete program to an abstract one. Each step takes a program and
produces a more abstract program together with a proof that the input refines the output.
Every property proved of the abstract program transports to the concrete one.

Ascent is built on the `Std.WP` weakest-precondition metatheory of the Lean toolchain.

## The judgment

`⦃P⦄ a ⊑[γ] c ⦃Q; E⦄` states that under the precondition `P` on the concrete initial state,
the concrete program `c` refines the abstract program `a`. The concretization
`γ : Concretization` maps abstract assertions to concrete ones, the coupling `Q` relates
abstract results to concrete results, and `E` relates thrown values. The triple is
`P ⊑ wrp γ a c Q E`, where

```
wrp γ a c Q E = ⨅ Qa Ea, γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (γ.ePost E Ea)
```

is the weakest refinement precondition: the weakest assertion under which every `wp` fact of
`a` transports to `c`. The `pure`, `bind`, `throw` and `tryCatch` laws of `wrp` are the rules a
forward simulation proof applies, one program construct at a time.

## Modules

* `Ascent/Corres/Basic.lean`: `Concretization`, its postcondition reification `post`, the
  functional state abstraction `ofStateRepr`, purification, identity and composition.
* `Ascent/Corres/Refinement.lean`: `wrp`, `Refinement`, the laws for `pure`, `bind`, `throw`
  and `tryCatch`, composition of refinements, and purification of a write-once program.
* `Ascent/Corres/Loop.lean`: the relational concretization `relRef` and the while-loop rule.
* `Ascent/Corres/SP.lean`: strongest postconditions as the lower adjoint of `wp`.
* `Ascent/UB.lean`, `Ascent/Loop.lean`: the undefined-behaviour effect, where a failed guard
  has weakest precondition `⊥`, and the while loop as a least fixpoint in it.
* `Ascent/WPMonadExact.lean`: monads whose `wp` computes `pure` and `bind` exactly, which the
  abstract side of a refinement needs.
* `Ascend/`: the `ascend` tactic and the `ascend_def` command. On a goal
  `⦃P⦄ (_ : AM AV) ⊑[γ] c ⦃Q; E⦄` the tactic computes the abstract program into the hole and
  proves the triple, leaving the verification conditions as goals. The command stores the
  abstract program as a definition `a` with the theorem `a.refines`. Rules are `Refinement`
  theorems registered with `@[ascend]`, keyed by the concrete program.
* `test/`: worked refinements, the `zip_with_add` case study, and negative tests.
* `bench/`: the synthesis benchmark harness.

## Build

`lean-toolchain` pins the nightly that ships `Std.WP`.

```
lake build
lake test
```
