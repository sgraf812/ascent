import Ascent.Demonic

/-!
# Strongest postconditions

`sp x P E` is the meet of all postconditions `Q` with `P ⊑ wp x Q E`. It is the lower adjoint
of `wp x · E` on preconditions that exclude failure, `P ⊑ wp x ⊤ E`, when `wp x` preserves
nonempty meets (`WPInfConjunctive`). The Galois connection is `sp_le_iff`.
-/

open Std.WP Lean.Order

universe i u v w z

namespace Ascent

/-- `wp x` preserves nonempty meets of postconditions. -/
class WPInfConjunctive (Prog : Type u) (Value : outParam (Type v)) (Pred : outParam (Type w))
    (EPosts : outParam (Type z)) [Assertion Pred] [Assertion EPosts]
    [WP Prog Value Pred EPosts] : Prop where
  /-- A nonempty meet of `wp`s is below the `wp` of the meet. -/
  iInf_wp_le_wp_iInf {ι : Type (max v w)} [Nonempty ι] (x : Prog) (Q : ι → Value → Pred)
    (E : EPosts) : iInf (fun j => wp x (Q j) E) ⊑ wp x (iInf Q) E

section
variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPosts : Type z}
  [Assertion Pred] [Assertion EPosts] [WP Prog Value Pred EPosts]

theorem wp_iInf_le_iInf_wp {ι : Type i} (x : Prog) (Q : ι → Value → Pred) (E : EPosts) :
    wp x (iInf Q) E ⊑ iInf (fun j => wp x (Q j) E) :=
  le_iInf _ _ fun j => WP.wp_monotone_post (x := x) (iInf_le Q j)

/-- The meet of all postconditions `Q` with `P ⊑ wp x Q E`. -/
noncomputable def sp (x : Prog) (P : Pred) (E : EPosts) : Value → Pred :=
  iInf fun Q : {Q : Value → Pred // P ⊑ wp x Q E} => Q.val

theorem sp_le {x : Prog} {P : Pred} {Q : Value → Pred} {E : EPosts} (h : P ⊑ wp x Q E) :
    sp x P E ⊑ Q :=
  iInf_le (fun Q : {Q : Value → Pred // P ⊑ wp x Q E} => Q.val) ⟨Q, h⟩

theorem le_sp {x : Prog} {P : Pred} {R : Value → Pred} {E : EPosts}
    (h : ∀ Q : Value → Pred, P ⊑ wp x Q E → R ⊑ Q) : R ⊑ sp x P E :=
  le_iInf _ _ fun Q => h Q.val Q.property

theorem sp_mono {x : Prog} {P P' : Pred} {E : EPosts} (h : P' ⊑ P) : sp x P' E ⊑ sp x P E :=
  le_sp fun _ hQ => sp_le (PartialOrder.rel_trans h hQ)

theorem le_wp_sp [WPInfConjunctive Prog Value Pred EPosts] {x : Prog} {P : Pred} {E : EPosts}
    (hdef : P ⊑ wp x ⊤ E) : P ⊑ wp x (sp x P E) E :=
  have : Nonempty {Q : Value → Pred // P ⊑ wp x Q E} := ⟨⟨⊤, hdef⟩⟩
  PartialOrder.rel_trans (le_iInf _ _ fun Q => Q.property)
    (WPInfConjunctive.iInf_wp_le_wp_iInf x
      (fun Q : {Q : Value → Pred // P ⊑ wp x Q E} => Q.val) E)

theorem le_wp_top {x : Prog} {P : Pred} {E : EPosts} (h : P ⊑ wp x (sp x P E) E) :
    P ⊑ wp x ⊤ E :=
  PartialOrder.rel_trans h (WP.wp_monotone_post (x := x) (le_top _))

theorem le_wp_top_of_le_wp {x : Prog} {P : Pred} {Q : Value → Pred} {E : EPosts}
    (h : P ⊑ wp x Q E) : P ⊑ wp x ⊤ E :=
  PartialOrder.rel_trans h (WP.wp_monotone_post (x := x) (le_top Q))

theorem sp_le_iff [WPInfConjunctive Prog Value Pred EPosts] {x : Prog} {P : Pred}
    {Q : Value → Pred} {E : EPosts} (hdef : P ⊑ wp x ⊤ E) :
    sp x P E ⊑ Q ↔ P ⊑ wp x Q E :=
  ⟨fun h => PartialOrder.rel_trans (le_wp_sp hdef) (WP.wp_monotone_post (x := x) h), sp_le⟩

end

instance {α : Type} : WPInfConjunctive (Demonic α) α Prop EStack⟨⟩ where
  iInf_wp_le_wp_iInf := by
    intro ι hne x Q E
    show iInf (fun j => x.wpD (Q j)) ⊑ x.wpD (iInf Q)
    rw [iInf_prop_eq_forall]
    intro h
    have hQ : iInf Q = fun a => ∀ j, Q j a := funext fun a => by rw [iInf_apply, iInf_prop_eq_forall]
    rw [hQ]
    exact (x.conj ι Q).mpr h

instance {m : Type u → Type v} {σ : Type u} {Pred : Type w} {EPosts : Type z} {α : Type u}
    [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts]
    [WPInfConjunctive (m (α × σ)) (α × σ) Pred EPosts] :
    WPInfConjunctive (StateT σ m α) α (σ → Pred) EPosts where
  iInf_wp_le_wp_iInf := by
    intro ι hne x Q E s
    simp only [iInf_apply, StateT.wp_apply_eq]
    refine PartialOrder.rel_trans
      (WPInfConjunctive.iInf_wp_le_wp_iInf (x.run s) (fun j p => Q j p.1 p.2) E)
      (WP.wp_monotone_post (x := x.run s) ?_)
    intro p
    simp only [iInf_apply]
    exact PartialOrder.rel_refl

end Ascent
