# Ascent

Ascent climbs from a concrete program to an abstract one. Each step takes a program and
produces a more abstract program together with a proof that the input refines the output.
Every property proved of the abstract program transports to the concrete one.

Ascent is built on the `Std.WP` weakest-precondition metatheory of the Lean toolchain.

## The judgment

`⦃P⦄ c ⪯[γ] a ⦃Q; E⦄` states that under the precondition `P` on the concrete initial state,
the concrete program `c` refines the abstract program `a`. The concretization
`γ : Concretization` maps abstract assertions to concrete ones, the return relation `Q`
relates concrete results to abstract results, and the exception relation `E` relates thrown
values. The triple is
`P ⊑ wrp γ c a Q E`, where

```
wrp γ c a Q E =
  ⨅ Qa Ea, γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (EPostsConcretization.ePosts γ E Ea)
```

is the weakest refinement precondition: the weakest assertion under which every `wp` fact of
`a` transports to `c`. The `pure`, `bind`, `throw` and `tryCatch` laws of `wrp` are the rules a
forward simulation proof applies, one program construct at a time.

## Modules

* `Ascent/WPMonadExact.lean`: monads whose `wp` computes `pure` and `bind` exactly, which the
  abstract side of a refinement needs.
* `Ascent/UB.lean`, `Ascent/UB/WhileLoop.lean`, `Ascent/UB/StateT.lean`: the undefined-behaviour
  effect, where a failed guard has weakest precondition `⊥`, the while loop as a least fixpoint
  in it, and `wp` lemmas for `StateT σ UB`.
* `Ascent/SP.lean`: strongest postconditions as the lower adjoint of `wp`.
* `Ascent/Concretization.lean`: `Concretization`, its postcondition reification `post`, the
  state abstractions `ofStateRepr` and `ofStateRel`, purification, identity and composition.
* `Ascent/EPostsConcretization.lean`: `EPostsConcretization`, the type of exception relations for
  a pair of exception stacks, and the concrete exception postconditions for an exception relation.
* `Ascent/WRP.lean`: `wrp` and its laws for `pure`, `bind`, `throw` and `tryCatch`.
* `Ascent/Refinement.lean`: `Refinement`, its notation, the triple forms of the laws,
  composition of refinements, and purification of a write-once program.
* `Ascent/Refinement/WhileLoop.lean`: the while-loop rule.
* `Ascent/Tactic/`: the `ascend` tactic and the `ascend_def` command. On a goal
  `⦃P⦄ c ⪯[γ] (_ : AM AV) ⦃Q; E⦄` the tactic computes the abstract program into the hole and
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
