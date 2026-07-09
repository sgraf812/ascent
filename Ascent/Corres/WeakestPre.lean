import Ascent.Corres.Basic

/-!
# The weakest boundary precondition

`corresPre r couple a c` internalizes a correspondence as a concrete-state predicate: the
weakest `pre` for which `Corres r ⟨pre, couple⟩ a c` holds (`corres_iff_le_corresPre`).
Instantiating `corres_bind`'s mid-condition with it turns the continuation obligation into the
theorem `corres_corresPre`, so `corres_bind_pre` and `corres_bind_erase_pre` need only the head
correspondence and one `wp` fact about the concrete head.
-/

open Std.Internal.Do Lean.Order

universe u v w w'

namespace Ascent

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WP CProg CVal CPred CEPred] [WP AProg AVal APred AEPred]

/-- The weakest boundary precondition of a correspondence, as a meet of Heyting implications:
under it, every abstract `wp` fact concretizes to the concrete `wp` at the coupled
postcondition. -/
noncomputable def corresPre (r : Concretization CPred APred CEPred AEPred)
    (couple : AVal → CVal → CPred) (a : AProg) (c : CProg) : CPred :=
  iInf fun Q : AVal → APred => iInf fun E : AEPred =>
    r.pred (wp a Q E) ⇨ wp c (r.post couple Q) (r.ePred E)

/-- A correspondence entails the weakest boundary precondition. -/
theorem Corres.le_corresPre {r : Concretization CPred APred CEPred AEPred}
    {b : Boundary CPred AVal CVal} {a : AProg} {c : CProg} (h : Corres r b a c) :
    b.pre ⊑ corresPre r b.couple a c :=
  le_iInf _ _ fun Q => le_iInf _ _ fun E =>
    himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm (h Q E))

/-- The weakest boundary precondition is a valid boundary precondition. -/
theorem corres_corresPre [Frame CPred] {r : Concretization CPred APred CEPred AEPred}
    {couple : AVal → CVal → CPred} {a : AProg} {c : CProg} :
    Corres r ⟨corresPre r couple a c, couple⟩ a c := fun Q E =>
  CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Q) (iInf_le _ E))

/-- Any entailment into the weakest boundary precondition is a correspondence. -/
theorem corres_of_le_corresPre [Frame CPred] {r : Concretization CPred APred CEPred AEPred}
    {pre : CPred} {couple : AVal → CVal → CPred} {a : AProg} {c : CProg}
    (hle : pre ⊑ corresPre r couple a c) : Corres r ⟨pre, couple⟩ a c := fun Q E =>
  PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) hle) (meet_le_right _ _))
    (corres_corresPre Q E)

/-- A correspondence is exactly an entailment into the weakest boundary precondition. -/
theorem corres_iff_le_corresPre [Frame CPred] {r : Concretization CPred APred CEPred AEPred}
    {pre : CPred} {couple : AVal → CVal → CPred} {a : AProg} {c : CProg} :
    Corres r ⟨pre, couple⟩ a c ↔ pre ⊑ corresPre r couple a c :=
  ⟨Corres.le_corresPre, corres_of_le_corresPre⟩

end

section
variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPred AEPred : Type w'}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPred] [Assertion AEPred]
  [WPMonad CM CPred CEPred] [WPMonad AM APred AEPred] [WPMonadExact AM APred AEPred]
  {r : Concretization CPred APred CEPred AEPred}

/-- The coupled values entail the relational weakest precondition of `pure` against `pure`. -/
theorem le_corresPre_pure {AV CV : Type w} {couple : AV → CV → CPred} (av : AV) (cv : CV) :
    couple av cv ⊑ corresPre r couple (pure av : AM AV) (pure cv : CM CV) := by
  refine le_iInf _ _ fun Q => le_iInf _ _ fun E => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (r.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_pure_le av Q E)))) ?_
  exact PartialOrder.rel_trans (le_iSup (fun av' => couple av' cv ⊓ r.pred (Q av')) av)
    (WPMonad.pure_le_wp_pure cv (r.post couple Q) (r.ePred E))

/-- The relational monad law: embedding the continuations' relational weakest precondition in
the value coupling bounds the `bind`s' relational weakest precondition. -/
theorem le_corresPre_bind [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    {couple₂ : AV₂ → CV₂ → CPred} :
    corresPre r (fun av cv => corresPre r couple₂ (a₂ av) (c₂ cv)) a₁ c₁ ⊑
      corresPre r couple₂ (a₁ >>= a₂) (c₁ >>= c₂) := by
  refine le_iInf _ _ fun Q => le_iInf _ _ fun E => ?_
  refine himp_complete _ _ _ (PartialOrder.rel_trans CompleteLattice.meet_le_comm ?_)
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (r.pred_mono ((‹WPMonadExact AM APred AEPred›).wp_bind_le a₁ a₂ Q E)))) ?_
  refine PartialOrder.rel_trans
    (CompleteLattice.meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ (fun av => wp (a₂ av) Q E)) (iInf_le _ E))) ?_
  refine PartialOrder.rel_trans
    (WP.wp_consequence c₁ _ (fun cv => wp (c₂ cv) (r.post couple₂ Q) (r.ePred E)) (r.ePred E) ?_)
    (WPMonad.bind_le_wp_bind c₁ c₂ (r.post couple₂ Q) (r.ePred E))
  intro cv
  show iSup (fun av => corresPre r couple₂ (a₂ av) (c₂ cv) ⊓ r.pred (wp (a₂ av) Q E)) ⊑ _
  refine iSup_le _ _ fun av => ?_
  exact CompleteLattice.meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Q) (iInf_le _ E))

/-- `corres_bind` at the weakest mid-condition: the continuation obligation is
`corres_corresPre`, leaving the head correspondence and one `wp` fact about the concrete
head. -/
theorem corres_bind_pre [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    [WPConjunctive (CM CV) CV CPred CEPred]
    (pre : CPred) (couple : CV → AV) (couple₂ : CV₂ → AV₂)
    {a₁ : AM AV} {c₁ : CM CV} {a₂ : AV → AM AV₂} {c₂ : CV → CM CV₂}
    (hc : Corres r (.eq pre couple) a₁ c₁)
    (hmid : pre ⊑
      wp c₁ (fun cv => corresPre r (coupleEq couple₂) (a₂ (couple cv)) (c₂ cv)) ⊥) :
    Corres r (.eq pre couple₂) (a₁ >>= a₂) (c₁ >>= c₂) :=
  corres_bind pre _ couple couple₂ hc hmid fun _ => corres_corresPre

/-- The erased-leaf `bind` at the weakest mid-condition. -/
theorem corres_bind_erase_pre [Frame CPred] {CV AV CV₂ AV₂ : Type w}
    [WPConjunctive (CM CV) CV CPred CEPred]
    (pre : CPred) (couple : CV → AV) (couple₂ : CV₂ → AV₂)
    {v : AV} {c₁ : CM CV} {a : AM AV₂} {c₂ : CV → CM CV₂}
    (hc : Corres r (.eq pre couple) (pure v : AM AV) c₁)
    (hmid : pre ⊑ wp c₁ (fun cv => corresPre r (coupleEq couple₂) a (c₂ cv)) ⊥) :
    Corres r (.eq pre couple₂) a (c₁ >>= c₂) :=
  corres_bind_erase pre _ couple couple₂ hc hmid fun _ => corres_corresPre

end

end Ascent
