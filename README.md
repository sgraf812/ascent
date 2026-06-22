# Ascent

Automatic abstraction of monadic programs with machine-checked correspondence proofs,
in the style of AutoCorres, read as abstract interpretation. Built on the
`Std.Internal.Do` weakest-precondition metatheory (`WP`, `PredTrans`, `Order`).

This is Phase A: the `Corres` metatheory and two worked refinement phases. The
`mcorres`/`ascend` tactic that synthesizes abstractions automatically is future work.

## Core

`Corres r γV a c` states that the abstract program `a` soundly abstracts the concrete
program `c`: every property proved of `a` transports to `c`. It is the abstract-interpretation
soundness statement `r.γP (wp a Q E) ⊑ wp c (r.γQ γV Q) (r.γE E)`, where `r : Refinement`
carries the monad-level concretizations `γP`/`γE` and `γV` is the per-occurrence value
abstraction.

* `Ascent/Corres/Basic.lean` — `Refinement`, `Corres`, the `LawfulRefinement` class (the
  `corres_pure`/`corres_bind` laws, keyed on the refinement) and the free structural lemmas.
  `Corres` is a category: `corres_id` is the identity (`idRefinement`), `corres_comp` the
  composition (`Refinement.comp`), exposed as a `Trans` instance for `calc`.
  `LawfulRefinement.ofWPMorphism` builds the laws from a proof that the abstract `wp` is a
  monad morphism (the common case); non-morphism abstractions provide a `LawfulRefinement`
  directly.
* `Ascent/Corres/TypeStrengthen.lean` — `ExceptT Unit (StateT σ Id) ↝ StateT σ Id`: a total
  failure-monad program abstracts to the pure state monad (`corres_lift`).
* `Ascent/Corres/WordAbstraction.lean` — `UInt64 ↝ Int`: value abstraction with no-overflow
  side-conditions, on the identity refinement.
* `test/` — worked example correspondences and negative tests (`lake test`).

## Build

The `lean-toolchain` pins the local `lean4` toolchain, which ships the `Std.Internal.Do`
metatheory (the per-program-type `WP` class). With that toolchain available to `elan`:

```
lake build
lake test
```
