import Ascent.UB

/-!
# Strongest postconditions from `wp`

`sp x P E` is the meet of all postconditions valid for the precondition `P`: the lower adjoint
of `wp x · E`. The counit `sp_le` holds unconditionally. The unit `le_wp_sp` needs `wp` to
preserve nonempty meets of postconditions (`WPInfConjunctive`) and `P` to exclude failure
(`P ⊑ wp x ⊤ E`); together they give the Galois connection `sp_le_iff`.
-/

open Std.Internal.Do Lean.Order

universe i u v w z

namespace Ascent

/-- `wp x` preserves nonempty meets of postconditions. Strengthens `WPConjunctive` from binary
to indexed meets; holds for deterministic and demonically nondeterministic interpretations. -/
class WPInfConjunctive (Prog : Type u) (Value : outParam (Type v)) (Pred : outParam (Type w))
    (EPred : outParam (Type z)) [Assertion Pred] [Assertion EPred]
    [WP Prog Value Pred EPred] : Prop where
  /-- A nonempty meet of `wp`s maps below the `wp` of the meet. -/
  iInf_wp_le_wp_iInf {ι : Type (max v w)} [Nonempty ι] (x : Prog) (Q : ι → Value → Pred)
    (E : EPred) : iInf (fun j => wp x (Q j) E) ⊑ wp x (iInf Q) E

section
variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]

/-- The converse meet inequality, from monotonicity alone. -/
theorem wp_iInf_le_iInf_wp {ι : Type i} (x : Prog) (Q : ι → Value → Pred) (E : EPred) :
    wp x (iInf Q) E ⊑ iInf (fun j => wp x (Q j) E) :=
  le_iInf _ _ fun j => WP.wp_consequence x _ _ E (iInf_le Q j)

/-- Strongest postcondition: the meet of all postconditions valid for `P` under `wp x · E`. -/
noncomputable def sp (x : Prog) (P : Pred) (E : EPred) : Value → Pred :=
  iInf fun Q : {Q : Value → Pred // P ⊑ wp x Q E} => Q.val

/-- Counit: `sp x P E` is below every postcondition valid for `P`. -/
theorem sp_le {x : Prog} {P : Pred} {Q : Value → Pred} {E : EPred} (h : P ⊑ wp x Q E) :
    sp x P E ⊑ Q :=
  iInf_le (fun Q : {Q : Value → Pred // P ⊑ wp x Q E} => Q.val) ⟨Q, h⟩

/-- Greatest-lower-bound introduction: below every valid postcondition means below `sp`. -/
theorem le_sp {x : Prog} {P : Pred} {R : Value → Pred} {E : EPred}
    (h : ∀ Q : Value → Pred, P ⊑ wp x Q E → R ⊑ Q) : R ⊑ sp x P E :=
  le_iInf _ _ fun Q => h Q.val Q.property

theorem sp_mono {x : Prog} {P P' : Pred} {E : EPred} (h : P' ⊑ P) : sp x P' E ⊑ sp x P E :=
  le_sp fun _ hQ => sp_le (PartialOrder.rel_trans h hQ)

/-- Unit: on a failure-free precondition, `P` entails the `wp` of its strongest postcondition. -/
theorem le_wp_sp [WPInfConjunctive Prog Value Pred EPred] {x : Prog} {P : Pred} {E : EPred}
    (hdef : P ⊑ wp x ⊤ E) : P ⊑ wp x (sp x P E) E :=
  have : Nonempty {Q : Value → Pred // P ⊑ wp x Q E} := ⟨⟨⊤, hdef⟩⟩
  PartialOrder.rel_trans (le_iInf _ _ fun Q => Q.property)
    (WPInfConjunctive.iInf_wp_le_wp_iInf x
      (fun Q : {Q : Value → Pred // P ⊑ wp x Q E} => Q.val) E)

/-- Failure-freedom is also necessary for the unit. -/
theorem le_wp_top {x : Prog} {P : Pred} {E : EPred} (h : P ⊑ wp x (sp x P E) E) :
    P ⊑ wp x ⊤ E :=
  PartialOrder.rel_trans h (WP.wp_consequence x _ _ E (le_top _))

/-- The Galois connection between `sp` and `wp`, on failure-free preconditions. -/
theorem sp_le_iff [WPInfConjunctive Prog Value Pred EPred] {x : Prog} {P : Pred}
    {Q : Value → Pred} {E : EPred} (hdef : P ⊑ wp x ⊤ E) :
    sp x P E ⊑ Q ↔ P ⊑ wp x Q E :=
  ⟨fun h => PartialOrder.rel_trans (le_wp_sp hdef) (WP.wp_consequence x _ _ E h), sp_le⟩

end

/-- `UB`'s `wp` preserves nonempty meets: it is evaluation at the result, `⊥` on failure. -/
instance {α : Type} : WPInfConjunctive (UB α) α Prop EPost.Nil where
  iInf_wp_le_wp_iInf := by
    intro ι hne x Q E
    cases x with
    | none =>
      obtain ⟨j⟩ := hne
      show iInf (fun j => wp (UB.fail : UB α) (Q j) E) ⊑ wp (UB.fail : UB α) (iInf Q) E
      simp only [UB.wp_fail_eq]
      exact iInf_le _ j
    | some a =>
      show iInf (fun j => wp (pure a : UB α) (Q j) E) ⊑ wp (pure a : UB α) (iInf Q) E
      simp only [UB.wp_pure_eq, iInf_apply]
      exact PartialOrder.rel_refl

/-- `StateT` lifts meet preservation from its base monad. -/
instance {m : Type u → Type v} {σ : Type u} {Pred : Type w} {EPred : Type z} {α : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [WPInfConjunctive (m (α × σ)) (α × σ) Pred EPred] :
    WPInfConjunctive (StateT σ m α) α (σ → Pred) EPred where
  iInf_wp_le_wp_iInf := by
    intro ι hne x Q E s
    simp only [iInf_apply, StateT.wp_apply_eq]
    refine PartialOrder.rel_trans
      (WPInfConjunctive.iInf_wp_le_wp_iInf (x.run s) (fun j p => Q j p.1 p.2) E)
      (WP.wp_consequence (x.run s) _ _ E ?_)
    intro p
    simp only [iInf_apply]
    exact PartialOrder.rel_refl

end Ascent
