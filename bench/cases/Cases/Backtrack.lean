import Cases.Setup.Blocks

/-!
# `Backtrack`: failing candidates before the rule that applies

The concrete program is a block of ten register writes `setC 7` on the toy block machine. The run
takes `k` candidate specs `wrp_setC_idx p` for `p < k` in its `distill [...]` list, at a priority
above the database. Each candidate asks for an abstraction of `7` under the relation `Idx p`, and no
rule abstracts `7` there, so the engine restores its state and passes to the next candidate, until
the rule `wrp_setC` of the database applies. The family stresses the spec backtracking on pure
premises, `k` times per step. No `vcgen` case corresponds to this family.
-/

open Std.WP Lean.Order Distillery DistillBench.Blocks
open Distillery.Concretization (ofStateRepr)

namespace DistillBench.Backtrack

def Idx (p c : BitVec 64) (j : Nat) : Prop := c = p + BitVec.ofNat 64 j

theorem wrp_setC_idx (p : BitVec 64) {v : BitVec 64} {j : Nat} {P : Prop}
    (_h : PureRefinement v j P (Idx p)) {Q : Unit → Unit → CS → Prop}
    {E : (Lbl → Lbl → CS → Prop) × EStack⟨⟩} :
    (fun t => P ∧ Q () () ⟨v, t.zf⟩)
      ⊑ wrp (ofStateRepr view) (setC v) (modifyIf (fun _ => True) fun _ => v : BlockM (BitVec 64) Unit) Q E := by
  intro t ht
  exact wrp_setC (Q := Q) (E := E) v t ht.2

attribute [distill] wrp_bind

noncomputable def block : Nat → BlockM CS Unit
  | 0 => setC 7
  | n+1 => do setC 7; block n

end DistillBench.Backtrack
