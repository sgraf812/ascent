import DistilleryTests.Setup.Blocks

/-!
# `distill_def` and `sym_simp_def`

Regressions of the two commands:
- a binder of type `Array Nat` elaborates with an assigned universe metavariable, which the added
  declarations instantiate (`a14ae3e`, `62af746`);
- the declarations are named in the current namespace (`0581e81`);
- the definition takes only the binders that its type or body uses, the theorem takes all
  (`423b076`);
- a refinement prints in its notation (`99e069f`).
-/

open Std.WP Lean.Order Distillery Distillery.Blocks
open Distillery.Concretization (ofStateRepr)

namespace Distillery.Blocks.Commands

attribute [local distill] wrp_bind wrp_pure

distill_def arr (a : Array Nat) (_unused : Nat) : BlockM (BitVec 64) Unit from
  ⦃fun _ => True⦄ (do setC (BitVec.ofNat 64 a.size); setC 0) ⪯[ofStateRepr view] arr
    ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄
  distill []

sym_simp_def arrS (a : Array Nat) (_unused : Nat) : Nat from a.size + 0 using pre [] post [Nat.add_zero]

/-- info: Distillery.Blocks.Commands.arr (a : Array Nat) : BlockM (BitVec 64) Unit -/
#guard_msgs in
#check Distillery.Blocks.Commands.arr

/-- info: Distillery.Blocks.Commands.arrS (a : Array Nat) : Nat -/
#guard_msgs in
#check Distillery.Blocks.Commands.arrS

/--
info: Distillery.Blocks.Commands.arr.refines (a : Array Nat) (_unused : Nat) :
  ⦃ fun x => True ⦄
    (do
      setC (BitVec.ofNat 64 a.size)
      setC 0) ⪯[ofStateRepr view]
    (arr a) ⦃ fun x x_1 x_2 => True; estack⟨fun l l' x => l = l'⟩ ⦄
-/
#guard_msgs in
#check Distillery.Blocks.Commands.arr.refines

example (a : Array Nat) (n : Nat) : a.size + 0 = arrS a := arrS.eq a n

end Distillery.Blocks.Commands
