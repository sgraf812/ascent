import Ascent.Refinement
import Kraken.X64.WP.Instance
import Kraken.X64.WP.Spec

open Std.WP Lean.Order Ascent
open scoped Program.WP

namespace Ascent.Kraken

variable [Host] [FunDecls]
  {AM : Type → Type} [Monad AM] {APred : Type} {AEPosts : Type} {ERels : Type}
  [Assertion APred] [Assertion AEPosts]
  [WPMonad AM APred AEPosts] [WPMonadExact AM APred AEPosts]
  [EPostsConcretization (MachineData → Prop) APred (Int64 → MachineData → Prop) AEPosts ERels]
  {γ : Concretization (MachineData → Prop) APred}

@[ascend] theorem wrp_cons {AV AV₂ : Type} (d : Directive) (p : Program) (a : AM AV) (k : AV → AM AV₂)
    {Q : Unit → AV₂ → MachineData → Prop} {E : ERels} (hN : Program.labels (d :: p) = []) :
    wrp γ d a (fun _ x => wrp γ p (k x) Q E) E ⊑ wrp γ (d :: p) (a >>= k) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPosts›).wp_bind_le a k Qa Ea)))) ?_
  refine PartialOrder.rel_trans
    (meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ (fun av => wp (k av) Qa Ea)) (iInf_le _ Ea))) ?_
  refine PartialOrder.rel_trans
    (WP.wp_monotone_post (x := d)
      (post' := fun _ => wp p (γ.post Q Qa) (EPostsConcretization.ePosts γ E Ea)) ?_) ?_
  · intro _
    show iSup (fun av => wrp γ p (k av) Q E ⊓ γ.pred (wp (k av) Qa Ea)) ⊑ _
    refine iSup_le _ _ fun av => ?_
    exact meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))
  · intro s hw
    exact Program.wp_cons hN hw

@[ascend] theorem wrp_nil {Q : Unit → Unit → MachineData → Prop} {E : ERels} :
    Q () () ⊑ wrp γ ([] : Program) (pure () : AM Unit) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, WPMonadExact.wp_pure_eq] at hs
  obtain ⟨hQ, hQa⟩ := hs
  refine Triple.le_wp Program.WP.Spec.nil s ?_
  show γ.post Q Qa () s
  simp only [Concretization.post, iSup_apply, iSup_prop_eq_exists, meet_apply, meet_prop_eq_and]
  exact ⟨(), hQ, hQa⟩

end Ascent.Kraken
