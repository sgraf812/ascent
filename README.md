# Distillery

Distillery draws an abstract program out of a concrete one. Each `distill_def` takes a program and
produces a more abstract program, together with a proof that the input refines the output. A chain
of such steps leads from machine code to a pure function, and every property proved of the last
program transports to the first.

Distillery is built on the `Std.WP` weakest-precondition metatheory of the Lean toolchain.

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

## The engine

`distill_def` states a refinement whose abstract program is a hole, and the tactic `distill`
computes the hole. The test `test/DistilleryTests/PureRefinement.lean` abstracts a chain of
`UInt64` additions to a chain of `Nat` additions:

```lean
def prog : Demonic UInt64 := do let a ← pure (7 : UInt64); let b ← pure (a + 7); pure (b + 7)

distill_def progN : Demonic Nat from
  ⦃(⊤ : Prop)⦄ prog ⪯[Concretization.id Prop] progN ⦃(⌜FunRel UInt64.toNat · ·⌝)⦄
  distill [prog]
```

The run unfolds `prog`, applies the rule `wrp_bind` at each `>>=` and the rule
`Refinement.pure_rel` at each `pure`. At each `pure`, it asks for an abstract value of the concrete
value. For `a + 7`, the rule `abs_add` abstracts the sum to `x + 7`, where `x` is the abstract value
of `a`, under the guard `x + 7 < 2 ^ 64`. The result is

```lean
def progN : Demonic Nat := do
  let x ← do Demonic.assert True; pure 7
  let x ← do Demonic.assert (x + 7 < 2 ^ 64); pure (x + 7)
  Demonic.assert (x + 7 < 2 ^ 64)
  pure (x + 7)
```

with the theorem `progN.refines : ⦃⊤⦄ prog ⪯[Concretization.id Prop] progN ⦃⌜FunRel UInt64.toNat · ·⌝⦄`.
The guards are part of the abstract program: a `Demonic.assert` that fails is undefined behaviour,
so a property of `progN` holds of `prog` only on the runs without overflow.

Three kinds of rules drive a run:

* `@[distill]` rules are `Refinement` theorems keyed by the concrete program, such as `wrp_bind`.
  The list of a run names definitions to unfold, such as `prog` above, and further rules. There the
  theorem `a.refines` of an earlier `distill_def` serves as a rule, for example the refinement of a
  callee at its call.
* `@[distill_pure]` rules are `PureRefinement` theorems, which relate a concrete value to an
  abstract value under a guard. `abs_add` above is one.
* `@[spec]` theorems of `vcgen` decompose a concrete step that has no abstract counterpart.

The verification conditions that remain go to the `with` step, a `grind` discharger.

`distill` is a fork of `vcgen`. A script translates the `vcgen` sources of the pinned toolchain,
and a series of nine patches adds the steps of synthesis. `docs/vcgen-fork.md` describes the
translation and each patch, with a test for each.

## Modules

* `Distillery/WPMonadExact.lean`: monads whose `wp` computes `pure` and `bind` exactly, which the
  abstract side of a refinement needs.
* `Distillery/Demonic.lean`, `Distillery/Demonic/WhileLoop.lean`, `Distillery/Demonic/StateT.lean`: the effect
  of abstract programs, monotone and finitely conjunctive predicate transformers, where undefined
  behaviour (`abort`, a failed `assert`) has weakest precondition `⊥` and an unspecified value
  (`select`, `unknown`) is a demonic choice; the while loop as a least fixpoint in the flat order,
  and `wp` lemmas for `StateT σ Demonic`.
* `Distillery/Concretization.lean`: `Concretization`, its postcondition reification `post`, the
  state abstractions `ofStateRepr` and `ofStateRel`, purification, identity and composition.
* `Distillery/EPostsConcretization.lean`: `EPostsConcretization`, the type of exception relations for
  a pair of exception stacks, and the concrete exception postconditions for an exception relation.
* `Distillery/WRP.lean`: `wrp` and its laws for `pure`, `bind`, `throw` and `tryCatch`.
* `Distillery/Refinement.lean`: `Refinement`, its notation, the triple forms of the laws,
  composition of refinements, and purification of a write-once program.
* `Distillery/Refinement/WhileLoop.lean`: the while-loop rule.
* `Distillery/Refinement/Lockstep.lean`, `Distillery/Refinement/Catch.lean`,
  `Distillery/Refinement/StateRepr.lean`: loops that refine step by step, the transport of a triple
  about a caught program, and the rules of the state abstraction `ofStateRepr`.
* `Distillery/PureRefinement.lean`: `PureRefinement`, the refinement of a pure concrete value by an
  abstract value under a guard.
* `Distillery/WPCont.lean`, `Distillery/FixLoop.lean`: continuity of `wp` along chains, and loops as
  least fixed points.
* `Distillery/Table.lean`, `Distillery/BlockLoop.lean`: tables of cells, and block programs whose
  jumps are exceptions, with the loop that runs them and their termination.
* `Distillery/Tactic/`: the `distill` tactic and the `distill_def` command. On a goal
  `⦃P⦄ c ⪯[γ] (_ : AM AV) ⦃Q; E⦄` the tactic computes the abstract program into the hole and
  proves the triple, leaving the verification conditions as goals. The command stores the
  abstract program as a definition `a` with the theorem `a.refines`. Rules are `Refinement`
  theorems registered with `@[distill]`, keyed by the concrete program.
* `test/`: worked refinements, the `zip_with_add` case study, and negative tests.
* `bench/`: the synthesis benchmark harness.
* `demo/`: pipelines from x64 text to pure functions for `zipWithAdd`, `memmove`, a binary search
  and an in-place reverse with a call, over the x64 model of kraken.

## Build

`lean-toolchain` pins the nightly that ships `Std.WP`.

```
lake build
lake test
```
