import Ascent.BlockLoop
import Ascent.Tactic.VCGen.Command

/-!
# The block loop and its structuring equations

`cfgLoop_header` makes a label the header of a loop over the other blocks: `loopAB` is a
two-block loop, and `twoBack` a header with two back edges. Structuring applies `cfgLoop_header`
at every label and pushes the headers' handlers to the literal throws: `chain` is a table of jumps
that evaluates to its last jump, `cycle` a two-block cycle that keeps one `repeat'` loop, and
`nested` an outer header whose handler crosses an inner loop by `tryCatch_forIn_bind`. These tables
run with the test `stay` that always holds.

In `ret` the state is a stack pointer and the loop stays while it is `0`. Block `1` sets the stack
pointer to `1` and jumps to the address `0`, which has a block: the loop leaves at `0` all the same.
-/

open Std.WP Lean.Order Ascent

namespace Ascent.BlockLoopTest

open BlockLoop

abbrev M := ExceptT Nat (StateT Bool UB)

def loopAB : Table Nat (M Unit) := [(0, throw 1), (1, throw 0)]

example : cfgLoop (fun _ => true) loopAB 0 = condState (fun _ => true) (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
    tryCatch (tryCatch (throw 1) (cfgLoop (fun _ => true) (loopAB.erase 0)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = 0 then condState (fun _ => true) (pure (ForInStep.yield PUnit.unit)) (throw l')
        else throw l'))) (throw 0) :=
  cfgLoop_header_of_some _ loopAB rfl

def header : M Unit := get >>= fun b => if b then throw 1 else throw 2

def twoBack : Table Nat (M Unit) := [(0, header), (1, throw 0), (2, throw 0)]

example : cfgLoop (fun _ => true) twoBack 0 = condState (fun _ => true) (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
    tryCatch (tryCatch header (cfgLoop (fun _ => true) (twoBack.erase 0)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = 0 then condState (fun _ => true) (pure (ForInStep.yield PUnit.unit)) (throw l')
        else throw l'))) (throw 0) :=
  cfgLoop_header_of_some _ twoBack rfl

def chain : Table Nat (M Unit) := [(0, throw 1), (1, throw 2), (2, throw 7)]

sym_simp_def chainS : M Unit from cfgLoop (fun _ => true) chain 0
  using pre [BlockLoop.tryCatch_throw, BlockLoop.tryCatch_tryCatch, tryCatch_forIn_bind, tryCatch_forIn]
  post [chain, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil, Option.isSome_some,
    Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw, BlockLoop.throw_bind,
    forIn_throw, ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.condState, condState_true, ne_eq, not_false_eq_true, implies_true, forall_const, or_true, true_or]

/-- info: def Ascent.BlockLoopTest.chainS : M Unit :=
throw 7 -/
#guard_msgs in
#print chainS

def cycle : Table Nat (M Unit) := [(0, throw 1), (1, throw 0)]

sym_simp_def cycleS : M Unit from cfgLoop (fun _ => true) cycle 0
  using pre [BlockLoop.tryCatch_throw, BlockLoop.throw_bind, BlockLoop.tryCatch_tryCatch,
    tryCatch_forIn_bind, tryCatch_forIn]
  post [cycle, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil, Option.isSome_some,
    Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw, BlockLoop.throw_bind,
    forIn_throw, ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.condState, condState_true, ne_eq, not_false_eq_true, implies_true, forall_const, or_true, true_or]

/-- info: def Ascent.BlockLoopTest.cycleS : M Unit :=
{ }.forIn PUnit.unit fun x x_1 => pure (ForInStep.yield PUnit.unit) -/
#guard_msgs in
#print cycleS

/-! The inner header `1` loops forever, and the handler of the outer header `0` crosses it: the
inner loop never throws `0`. -/

def nested : Table Nat (M Unit) := [(0, throw 1), (1, throw 1)]

sym_simp_def nestedS : M Unit from cfgLoop (fun _ => true) nested 0
  using pre [BlockLoop.tryCatch_throw, BlockLoop.throw_bind, BlockLoop.tryCatch_tryCatch,
    BlockLoop.tryCatch_pure, tryCatch_forIn_bind, tryCatch_map_forIn, tryCatch_forIn]
  post [nested, forIn_bind_done, bind_pure_unit, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil, Option.isSome_some,
    Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw, BlockLoop.throw_bind,
    forIn_throw, ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.forIn,
    ThrowsOnly.tryCatch, ThrowsOnly.condState, condState_true, ne_eq, not_false_eq_true, implies_true, forall_const, or_true, true_or]

/-- info: def Ascent.BlockLoopTest.nestedS : M Unit :=
{ }.forIn PUnit.unit fun x x_1 => pure (ForInStep.yield PUnit.unit) -/
#guard_msgs in
#print nestedS

abbrev N := ExceptT Nat (StateT Nat UB)

theorem tryCatch_set_bind {β : Type} (t : Nat) (k : PUnit → N β) (h : Nat → N β) :
    tryCatch (set t >>= k) h = set t >>= fun u => tryCatch (k u) h := rfl

theorem set_bind_condState {β : Type} (t : Nat) (c : Nat → Bool) (x y : N β) :
    (set t >>= fun _ => condState c x y) = (set t >>= fun _ => if c t then x else y) := rfl

def ret : Table Nat (N Unit) := [(0, throw 1), (1, set 1 >>= fun _ => throw 0)]

sym_simp_def retS : N Unit from cfgLoop (· == 0) ret 0
  using pre [BlockLoop.tryCatch_throw, BlockLoop.throw_bind, BlockLoop.tryCatch_tryCatch,
    tryCatch_set_bind, tryCatch_condState, condState_bind, set_bind_condState]
  post [ret, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil, Option.isSome_some,
    Option.isSome_none, Option.getD_some, cfgLoop_header, cfgLoop_eq_throw, BlockLoop.throw_bind,
    bind_assoc, forIn_bind_throw, forIn_throw, condState_condState_left, condState_condState_right,
    Nat.reduceBEq, Nat.reduceEqDiff, Bool.false_eq_true, ite_false, ite_true, reduceIte]

/-- info: def Ascent.BlockLoopTest.retS : N Unit :=
condState (fun x => x == 0)
  ({ }.forIn PUnit.unit fun x x_1 =>
    condState (fun x => x == 0)
      (do
        set 1
        throw 0)
      (throw 1))
  (throw 0) -/
#guard_msgs in
#print retS

end Ascent.BlockLoopTest
