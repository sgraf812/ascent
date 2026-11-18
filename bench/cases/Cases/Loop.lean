import Cases.Setup.Blocks
import Distillery.Refinement.Lockstep

/-!
# `Loop`: one lockstep loop with a long body

The concrete program is one `FixLoop` loop on the toy block machine, whose body runs `n` register
writes `setC` and yields. The run applies `wrp_forIn_lockstep`, whose invariant comes from the
`invariants` section of the invocation, and synthesizes the abstract body. The family stresses the
loop rule, the invariant hole and a body of `n` steps under one invariant. No `vcgen` case
corresponds to this family.
-/

open Std.WP Lean.Order Distillery DistillBench.Blocks
open Distillery.Concretization (ofStateRepr)

namespace DistillBench.Loop

attribute [distill] wrp_bind

@[distill] theorem wrp_pure_unit {Q : Unit → Unit → CS → Prop} {E : (Lbl → Lbl → CS → Prop) × EStack⟨⟩} :
    Q () () ⊑ wrp (ofStateRepr view) (pure () : BlockM CS Unit) (pure () : BlockM (BitVec 64) Unit) Q E :=
  wrp_pure () ()

noncomputable def body : Nat → BlockM CS Unit
  | 0 => pure ()
  | n+1 => do setC (BitVec.ofNat 64 n); body n

noncomputable def bodyA : Nat → BlockM (BitVec 64) Unit
  | 0 => pure ()
  | n+1 => do modifyIf (fun _ => True) (fun _ => BitVec.ofNat 64 n); bodyA n

end DistillBench.Loop
