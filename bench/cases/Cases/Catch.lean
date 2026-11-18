import Distillery.Refinement
import Distillery.Tactic.VCGen.Command

/-!
# `Catch`: nested handlers

The concrete program `catchN n 0` in `Except Nat Nat` throws `0` under `n` nested `tryCatch`
handlers, and each handler rethrows its exception plus one. The abstract program is a nest of the
same depth under `Concretization.id Prop`. The rule `wrp_tryCatch` rebinds the exception relation
with the `wrp` of the handlers, and the rule `wrp_throw_same` throws the concrete value. Each
abstract handler is applied to a closed thrown value, so the run fills it with a constant function.
The family stresses the exception relation, which grows by one handler per level. No `vcgen` case
corresponds to this family.
-/

open Std.WP Lean.Order Distillery

namespace DistillBench.Catch

abbrev γe : Concretization Prop Prop := Concretization.id Prop

theorem wrp_throw_same (e : Nat) {Q : Nat → Nat → Prop} {E : Nat → Nat → Prop} :
    E e e ⊑ wrp γe (MonadExceptOf.throw e : Except Nat Nat) (MonadExceptOf.throw e : Except Nat Nat) Q E :=
  wrp_throw e e

attribute [distill] wrp_throw_same wrp_tryCatch

def catchN : Nat → Nat → Except Nat Nat
  | 0, x => MonadExceptOf.throw x
  | n+1, x => MonadExceptOf.tryCatch (catchN n x) fun e => MonadExceptOf.throw (e + 1)

end DistillBench.Catch
