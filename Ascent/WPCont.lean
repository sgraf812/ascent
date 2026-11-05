import Std.WP

/-!
# Continuity of `wp`

`WPCont Prog` relates the `CCPO` of a program type `Prog` to its `WP` interpretation. For a chain
`ch` of programs, `wp` of the supremum is below the supremum of the `wp`s:

```
wp (CCPO.csup hch) Q E ⊑ ⨆ x : {x // ch x}, wp x.1 Q E
```

A `partial_fixpoint` definition is the supremum of a chain of its finite unfoldings, so fixpoint
induction over it needs this fact. `StateT`, `ExceptT` and `OptionT` lift `WPCont` from the base
program type.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

/-- `wp` of the supremum of a chain of programs is below the supremum of their `wp`s. -/
class WPCont (Prog : Type u) {Value : outParam (Type v)} {Pred : outParam (Type w)}
    {EPosts : outParam (Type w')} [CCPO Prog] [Assertion Pred] [Assertion EPosts]
    [WP Prog Value Pred EPosts] : Prop where
  wp_csup {ch : Prog → Prop} (hch : chain ch) (Q : Value → Pred) (E : EPosts) :
    wp (CCPO.csup hch) Q E ⊑ iSup fun x : {x // ch x} => wp x.1 Q E

end Ascent

open Ascent

instance {σ α : Type u} {m : Type u → Type v} [CCPO (m (α × σ))] : CCPO (StateT σ m α) :=
  instCCPOPi

instance {ε α : Type u} {m : Type u → Type v} [CCPO (m (Except ε α))] : CCPO (ExceptT ε m α) :=
  inferInstanceAs (CCPO (m (Except ε α)))

instance {σ α : Type u} {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'}
    [CCPO (m (α × σ))] [Assertion Pred] [Assertion EPosts] [WP (m (α × σ)) (α × σ) Pred EPosts]
    [WPCont (m (α × σ))] : WPCont (StateT σ m α) where
  wp_csup {ch} hch Q E s := by
    change wp ((CCPO.csup hch : StateT σ m α) s) (fun p : α × σ => Q p.1 p.2) E ⊑ _
    rw [← fun_csup_eq ch hch]
    refine PartialOrder.rel_trans (WPCont.wp_csup (chain_apply hch s) _ E) ?_
    refine iSup_le _ _ ?_
    rintro ⟨_, f, hf, rfl⟩
    rw [iSup_apply]
    exact le_iSup (fun x : {x // ch x} => wp x.1 Q E s) ⟨f, hf⟩

instance {ε α : Type u} {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'}
    [∀ α, CCPO (m α)] [Assertion Pred] [Assertion EPosts]
    [WP (m (Except ε α)) (Except ε α) Pred EPosts] [WPCont (m (Except ε α))] :
    WPCont (ExceptT ε m α) where
  wp_csup hch _ E := WPCont.wp_csup (Prog := m (Except ε α)) hch _ E.2

instance {α : Type u} {m : Type u → Type v} {Pred : Type u} {EPosts : Type w'}
    [∀ α, CCPO (m α)] [Assertion Pred] [Assertion EPosts]
    [WP (m (Option α)) (Option α) Pred EPosts] [WPCont (m (Option α))] :
    WPCont (OptionT m α) where
  wp_csup hch _ E := WPCont.wp_csup (Prog := m (Option α)) hch _ E.2
