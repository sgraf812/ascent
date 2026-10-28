import Ascent.EPostsCoupling

/-!
# The weakest refinement precondition

`wrp γ c a Q E` is the weakest concrete assertion under which the concrete program `c` refines
the abstract program `a`:

```
wrp γ c a Q E = ⨅ Qa Ea, γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (EPostsCoupling.ePosts γ E Ea)
```

For every abstract postcondition `Qa` and exception postconditions `Ea`, if `a` establishes
them, then `c` establishes their concretization. `Q : CVal → AVal → CPred` couples returned
values, and `E` couples thrown values.

The laws of `wrp` follow the laws of `wp`. `wrp_pure` consumes `Q`, and `wrp_bind` rebinds `Q`
with the `wrp` of the continuations. `wrp_throw` consumes `E`, and `wrp_tryCatch` rebinds `E`
with the `wrp` of the handlers.
-/

open Std.WP Lean.Order

namespace Ascent

universe u v w w'

theorem meet_iSup_le {l : Type w} [Assertion l] [Heyting l] {ι : Sort _} (x : l) (f : ι → l) :
    x ⊓ iSup f ⊑ iSup fun i => x ⊓ f i :=
  PartialOrder.rel_trans
    (meet_mono_right (iSup_le _ _ fun i =>
      le_himp_of_meet_le_left (le_iSup (fun i => x ⊓ f i) i)))
    meet_himp_le

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPosts AEPosts : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [instA : WP AProg AVal APred AEPosts]
  [EPostsCoupling CPred APred CEPosts AEPosts Ξ]

/-- The weakest concrete assertion under which `c` refines `a`: every `wp` fact of `a`
transports to `c` through `γ`, `Q` and `E`. -/
noncomputable def wrp (γ : Concretization CPred APred)
    (c : CProg) (a : AProg) (Q : CVal → AVal → CPred) (E : Ξ) : CPred :=
  iInf fun Qa : AVal → APred => iInf fun Ea : AEPosts =>
    γ.pred (wp a Qa Ea) ⇨ wp c (γ.post Q Qa) (EPostsCoupling.ePosts γ E Ea)

end

section
variable {CProg AProg : Type _} {CVal AVal : Type _}
  {CPred APred : Type w} {CEPosts AEPosts : Type w'} {Ξ : Type u}
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WP CProg CVal CPred CEPosts] [instA : WP AProg AVal APred AEPosts]
  [EPostsCoupling CPred APred CEPosts AEPosts Ξ]

variable {γ : Concretization CPred APred} {P : CPred}
  {c : CProg} {a : AProg} {Q : CVal → AVal → CPred} {E : Ξ}

theorem wrp_intro
    (h : ∀ (Qa : AVal → APred) (Ea : AEPosts),
      P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (EPostsCoupling.ePosts γ E Ea)) :
    P ⊑ wrp γ c a Q E :=
  le_iInf _ _ fun Qa => le_iInf _ _ fun Ea =>
    le_himp_of_meet_le_left (PartialOrder.rel_trans meet_le_comm (h Qa Ea))

theorem wrp_transport [Heyting CPred] (h : P ⊑ wrp γ c a Q E)
    (Qa : AVal → APred) (Ea : AEPosts) :
    P ⊓ γ.pred (wp a Qa Ea) ⊑ wp c (γ.post Q Qa) (EPostsCoupling.ePosts γ E Ea) :=
  meet_le_of_le_himp
    (PartialOrder.rel_trans h (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea)))

theorem wrp_mono_post [Heyting CPred] {Q' : CVal → AVal → CPred}
    (hQ : ∀ cv av, Q cv av ⊑ Q' cv av) : wrp γ c a Q E ⊑ wrp γ c a Q' E := by
  refine iInf_mono fun Qa => iInf_mono fun Ea => ?_
  refine himp_mono PartialOrder.rel_refl ?_
  refine WP.wp_monotone_post (x := c) ?_
  intro cv
  refine iSup_le _ _ fun av => ?_
  exact PartialOrder.rel_trans
    (le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (hQ cv av)) (meet_le_right _ _))
    (le_iSup (fun av' => Q' cv av' ⊓ γ.pred (Qa av')) av)

theorem wrp_anti [Heyting CPred] {W : WP AProg AVal APred AEPosts}
    (h : ∀ (a : AProg) Qa Ea, W.wp a Qa Ea ⊑ instA.wp a Qa Ea) :
    wrp (instA := instA) γ c a Q E ⊑ wrp (instA := W) γ c a Q E :=
  iInf_mono fun Qa => iInf_mono fun Ea => himp_mono (γ.pred_mono (h a Qa Ea)) PartialOrder.rel_refl

end

section
variable {CM AM : Type w → Type v} {CPred APred : Type w} {CEPosts AEPosts : Type w'} {Ξ : Type u}
  [Monad CM] [Monad AM]
  [Assertion CPred] [Assertion APred] [Assertion CEPosts] [Assertion AEPosts]
  [WPMonad CM CPred CEPosts] [WPMonad AM APred AEPosts] [WPMonadExact AM APred AEPosts]
  [EPostsCoupling CPred APred CEPosts AEPosts Ξ]
  {γ : Concretization CPred APred}

theorem wrp_pure {CV AV : Type w} {Q : CV → AV → CPred} {E : Ξ} (cv : CV) (av : AV) :
    Q cv av ⊑ wrp γ (pure cv : CM CV) (pure av : AM AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPosts›).wp_pure_le av Qa Ea)))) ?_
  exact PartialOrder.rel_trans (le_iSup (fun av' => Q cv av' ⊓ γ.pred (Qa av')) av)
    (WPMonad.pure_le_wp_pure cv (γ.post Q Qa) (EPostsCoupling.ePosts γ E Ea))

theorem wrp_bind [Heyting CPred] {CV AV CV₂ AV₂ : Type w}
    {c₁ : CM CV} {a₁ : AM AV} {c₂ : CV → CM CV₂} {a₂ : AV → AM AV₂}
    {Q : CV₂ → AV₂ → CPred} {E : Ξ} :
    wrp γ c₁ a₁ (fun cv av => wrp γ (c₂ cv) (a₂ av) Q E) E ⊑
      wrp γ (c₁ >>= c₂) (a₁ >>= a₂) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  refine PartialOrder.rel_trans (le_meet _ _ _ (meet_le_left _ _)
    (PartialOrder.rel_trans (meet_le_right _ _)
      (γ.pred_mono ((‹WPMonadExact AM APred AEPosts›).wp_bind_le a₁ a₂ Qa Ea)))) ?_
  refine PartialOrder.rel_trans
    (meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ (fun av => wp (a₂ av) Qa Ea)) (iInf_le _ Ea))) ?_
  refine PartialOrder.rel_trans
    (WP.wp_monotone_post (x := c₁)
      (post' := fun cv => wp (c₂ cv) (γ.post Q Qa) (EPostsCoupling.ePosts γ E Ea)) ?_)
    (WPMonad.bind_le_wp_bind c₁ c₂ (γ.post Q Qa) (EPostsCoupling.ePosts γ E Ea))
  intro cv
  show iSup (fun av => wrp γ (c₂ cv) (a₂ av) Q E ⊓ γ.pred (wp (a₂ av) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun av => ?_
  exact meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

/-- The `wrp` of the continuations `c₂` and `a₂`, as a coupling on their inputs. -/
noncomputable def wrpCont {CV AV CV₂ AV₂ : Type w}
    (γ : Concretization CPred APred)
    (c₂ : CV → CM CV₂) (a₂ : AV → AM AV₂) (Q : CV₂ → AV₂ → CPred) (E : Ξ) :
    CV → AV → CPred :=
  fun cv av => wrp γ (c₂ cv) (a₂ av) Q E

end

/-! ## Exceptions, for `Except` -/

section
variable {εc εa CV AV : Type}
  {γ : Concretization Prop Prop}

theorem wrp_throw {Q : CV → AV → Prop} {E : εc → εa → Prop} (ec : εc) (ea : εa) :
    E ec ea ⊑
      wrp γ (MonadExceptOf.throw ec : Except εc CV)
        (MonadExceptOf.throw ea : Except εa AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  simp only [WPMonad.wp_throw_Except_apply_eq, EPostsCoupling.ePosts_fun]
  exact le_iSup_of_le ea PartialOrder.rel_refl

theorem wrp_tryCatch {Q : CV → AV → Prop} {E : εc → εa → Prop}
    {cx : Except εc CV} {ax : Except εa AV}
    {ch : εc → Except εc CV} {ah : εa → Except εa AV} :
    wrp γ cx ax Q (fun ec ea => wrp γ (ch ec) (ah ea) Q E) ⊑
      wrp γ (MonadExceptOf.tryCatch cx ch) (MonadExceptOf.tryCatch ax ah) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  simp only [WPMonad.wp_tryCatch_Except_apply_eq]
  refine PartialOrder.rel_trans
    (meet_le_of_le_himp
      (PartialOrder.rel_trans (iInf_le _ Qa)
        (iInf_le _ (fun ea => wp (ah ea) Qa Ea)))) ?_
  refine WP.wp_monotone (x := cx) PartialOrder.rel_refl ?_
  intro ec
  show iSup (fun ea => wrp γ (ch ec) (ah ea) Q E ⊓ γ.pred (wp (ah ea) Qa Ea)) ⊑ _
  refine iSup_le _ _ fun ea => ?_
  exact meet_le_of_le_himp
    (PartialOrder.rel_trans (iInf_le _ Qa) (iInf_le _ Ea))

/-- The `wrp` of the handlers `ch` and `ah`, as a coupling on thrown values. -/
noncomputable def wrpECont
    (γ : Concretization Prop Prop)
    (ch : εc → Except εc CV) (ah : εa → Except εa AV) (Q : CV → AV → Prop)
    (E : εc → εa → Prop) : εc → εa → Prop :=
  fun ec ea => wrp γ (ch ec) (ah ea) Q E

end

end Ascent
