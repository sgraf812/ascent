import Ascent.BlockLoop

/-!
# Catching an exit between two refinements

A block program `b` leaves through the exception `e`, and the next layer refines the program
`tryCatch b (fun l => if l = e then pure () else throw l)`, which returns where `b` leaves through
`e`. `Refinement.transport_catch` transports a triple about the abstract program over both
refinements: the abstract postcondition at the return of the caught program becomes the concrete
exception postcondition at `e`, and every other exception keeps its exception postcondition.
-/

open Std.WP Lean.Order

namespace Ascent

section
variable {κ σ : Type} [DecidableEq κ] {CProg AProg CVal AVal : Type _}
  {CPred APred CEPosts AEPosts : Type} {ERels₁ ERels₂ : Type _}
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [WP AProg AVal APred AEPosts]
  [EPostsConcretization CPred (σ → Prop) CEPosts ((κ → σ → Prop) × EStack⟨⟩) ERels₁]
  [EPostsConcretization (σ → Prop) APred ((κ → σ → Prop) × EStack⟨⟩) AEPosts ERels₂]
  [Heyting CPred]

theorem Refinement.transport_catch {e : κ}
    {γ₁ : Concretization CPred (σ → Prop)} {γ₂ : Concretization (σ → Prop) APred}
    {P : CPred} {P_B : σ → Prop} {Q₁ : CVal → Unit → CPred} {Q₂ : Unit → AVal → σ → Prop}
    {E₁ : ERels₁} {E₂ : ERels₂} {c : CProg} {b : ExceptT κ (StateT σ UB) Unit} {a : AProg}
    {Pa : APred} {Qa : AVal → APred} {Ea : AEPosts}
    (h₁ : ⦃P⦄ c ⪯[γ₁] b ⦃Q₁; E₁⦄)
    (h₂ : ⦃P_B⦄ (MonadExcept.tryCatch b (fun l => if l = e then Pure.pure () else MonadExcept.throw l)) ⪯[γ₂] a ⦃Q₂; E₂⦄)
    (ha : Triple a Pa Qa Ea) :
    Triple c (P ⊓ γ₁.pred (P_B ⊓ γ₂.pred Pa)) (γ₁.post Q₁ (γ₂.post Q₂ Qa))
      (EPostsConcretization.ePosts γ₁ E₁
        ((fun l s => if l = e then γ₂.post Q₂ Qa () s
          else (EPostsConcretization.ePosts γ₂ E₂ Ea : (κ → σ → Prop) × EStack⟨⟩).1 l s,
         (EPostsConcretization.ePosts γ₂ E₂ Ea : (κ → σ → Prop) × EStack⟨⟩).2) :
          (κ → σ → Prop) × EStack⟨⟩)) := by
  have hb := h₂.transport ha
  refine h₁.transport ⟨fun s hs => ?_⟩
  have h := hb.le_wp s hs
  rw [BlockLoop.wp_tryCatch] at h
  refine WP.wp_monotone_epost (x := b) ?_ s h
  refine Prod.mk_le _ _ _ (fun l t ht => ?_) PartialOrder.rel_refl
  by_cases hl : l = e
  · subst hl
    simpa [WPMonadExact.wp_pure_eq] using ht
  · simpa [hl, BlockLoop.wp_throw] using ht

end

end Ascent
