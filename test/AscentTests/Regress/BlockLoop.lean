import Ascent.BlockLoop
import Ascent.Tactic.VCGen.Command

/-!
# The block loop and its structuring equations

`cfgLoop_elim` structures a loop at a label: `loopAB` is a two-block loop, and `twoBack` a header
with two back edges. `cfgLoop_eq_tryCatch` runs a label once when no block of the table without it
returns to it: `chain` is a table of jumps that `sym_simp_def` evaluates to its last jump, and
`cycle` is a two-block cycle whose structuring keeps one `repeat'` loop at the header. Both runs
discharge `ThrowsOnly` side conditions several levels deep.
-/

open Std.WP Lean.Order Ascent

namespace Ascent.BlockLoopTest

abbrev M := ExceptT Nat (StateT Bool UB)

def loopAB : Table Nat (M Unit) := [(0, throw 1), (1, throw 0)]

example : cfgLoop loopAB 0 = FixLoop.mk.forIn PUnit.unit (cfgIter loopAB 0 (throw 1)) :=
  cfgLoop_elim loopAB rfl

def header : M Unit := get >>= fun b => if b then throw 1 else throw 2

def twoBack : Table Nat (M Unit) := [(0, header), (1, throw 0), (2, throw 0)]

example : cfgLoop twoBack 0 = FixLoop.mk.forIn PUnit.unit (cfgIter twoBack 0 header) :=
  cfgLoop_elim twoBack rfl

def chain : Table Nat (M Unit) := [(0, throw 1), (1, throw 2), (2, throw 7)]

sym_simp_def chainS : M Unit from cfgLoop chain 0
  using pre [BlockLoop.tryCatch_throw, cfgLoop_eq_tryCatch]
  post [chain, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil, Option.isSome_some,
    Option.isSome_none, Option.getD_some, cfgLoop_eq_tryCatch, cfgLoop_eq_forIn, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.forIn, ne_eq, not_false_eq_true,
    implies_true, forall_const]

/-- info: def Ascent.BlockLoopTest.chainS : M Unit :=
throw 7 -/
#guard_msgs in
#print chainS

def cycle : Table Nat (M Unit) := [(0, throw 1), (1, throw 0)]

sym_simp_def cycleS : M Unit from cfgLoop cycle 0
  using pre [BlockLoop.tryCatch_throw, BlockLoop.throw_bind, cfgLoop_eq_tryCatch]
  post [cycle, Table.get?_cons, Table.get?_nil, Table.erase_cons, Table.erase_nil, Option.isSome_some,
    Option.isSome_none, Option.getD_some, cfgLoop_eq_tryCatch, cfgLoop_eq_forIn, cfgLoop_eq_throw,
    ThrowsOnly.pure, ThrowsOnly.throw, ThrowsOnly.bind, ThrowsOnly.forIn, ne_eq, not_false_eq_true,
    implies_true, forall_const, BlockLoop.throw_bind]

/-- info: def Ascent.BlockLoopTest.cycleS : M Unit :=
{ }.forIn PUnit.unit fun x x_1 => pure (ForInStep.yield PUnit.unit) -/
#guard_msgs in
#print cycleS

end Ascent.BlockLoopTest
