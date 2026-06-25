import Ascent.Loop
import Ascent.Corres.StateT

/-!
# A general while-loop correspondence

The loop body mutates the loop counter, so a *fixed* state coupling cannot span the loop. The
correspondence is therefore stated against a **relational** refinement `relRef J`, where
`J : Aσ → Cσ → Prop` couples an abstract and a concrete state. The relation is invariant across
iterations even though the coupled *values* change.

`corres_whileLoop` reduces a loop correspondence to: the guards agree under `J`, the body
corresponds (preserving `J`), and the body strictly decreases an abstract variant `μ`. It is proved
by strong induction on `μ`, unfolding both loops one step at a time.
-/

open Std.Internal.Do Lean.Order Ascent

/-- A refinement from a state relation `J`: an abstract assertion `P` concretizes to "there is a
`J`-related abstract state on which `P` holds". -/
def relRef {Aσ Cσ : Type} (J : Aσ → Cσ → Prop) :
    Refinement (Cσ → Prop) (Aσ → Prop) EPost.Nil EPost.Nil where
  γP P := fun cs => ∃ as, J as cs ∧ P as
  γE := id
  γP_mono h := fun _ ⟨as, hJ, hP⟩ => ⟨as, hJ, h as hP⟩
  γE_mono h := h

@[simp] theorem relRef_γP {Aσ Cσ} (J : Aσ → Cσ → Prop) (P : Aσ → Prop) :
    (relRef J).γP P = fun cs => ∃ as, J as cs ∧ P as := rfl

@[simp] theorem relRef_γQ {Aσ Cσ CV AV} (J : Aσ → Cσ → Prop) (f : CV → AV) (Q : AV → Aσ → Prop) :
    (relRef J).γQ (αVeq f) Q = fun cv cs => ∃ as, J as cs ∧ Q (f cv) as := by
  simp only [Refinement.γQ_αVeq, relRef_γP]

/-- A relational refinement transports `pure`/`bind`: it needs only the abstract monad's
(`StateT Aσ UB`) `wp` facts, which hold regardless of `J`. -/
instance {Aσ Cσ : Type} (J : Aσ → Cσ → Prop) :
    LawfulRefinement (relRef J) (StateT Cσ UB) (StateT Aσ UB) where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun x f post E => by
    intro s; exact UB.wp_bind_le (x s) (fun p => f p.1 p.2) (fun p => post p.1 p.2) E

/-- One-step unfolding of `whileLoop`'s `wp`. -/
theorem wp_whileLoop {σ} (cond : σ → Bool) (body : StateT σ UB Unit)
    (Q : Unit → σ → Prop) (E : EPost.Nil) (s : σ) :
    wp (whileLoop cond body) Q E s
      = if cond s then wp body (fun _ s' => wp (whileLoop cond body) Q E s') E s else Q () s := by
  rw [whileLoop, StateT.wp_apply_eq, StateT.run, loopFix]
  simp only [wp_ite, UB.wp_bind_eq, UB.wp_pure_eq, StateT.wp_apply_eq, StateT.run]

/-- The loop correspondence: under a state relation `J`, if the guards agree, the body corresponds
(preserving `J`), and the body strictly decreases an abstract variant `μ`, then the loops
correspond. By strong induction on `μ`. -/
theorem corres_whileLoop {Aσ Cσ : Type} (J : Aσ → Cσ → Prop)
    (acond : Aσ → Bool) (abody : StateT Aσ UB Unit)
    (ccond : Cσ → Bool) (cbody : StateT Cσ UB Unit)
    (μ : Aσ → Nat)
    (hcond : ∀ as cs, J as cs → acond as = ccond cs)
    (hbody : Corres (relRef J) ⊤ (αVeq (id : Unit → Unit)) abody cbody)
    (hμ : ∀ (E : EPost.Nil) as, acond as = true → wp abody (fun _ _ => True) E as →
        wp abody (fun _ as' => μ as' < μ as) E as) :
    Corres (relRef J) ⊤ (αVeq (id : Unit → Unit)) (whileLoop acond abody) (whileLoop ccond cbody) := by
  intro Q E cs hcs
  simp only [top_meet] at hcs
  obtain ⟨as, hJ, hwp⟩ := hcs
  suffices H : ∀ n as cs, μ as < n → J as cs → wp (whileLoop acond abody) Q E as →
      wp (whileLoop ccond cbody) ((relRef J).γQ (αVeq id) Q) E cs by
    exact H (μ as + 1) as cs (Nat.lt_succ_self _) hJ hwp
  intro n
  induction n with
  | zero => intro as cs hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro as cs hlt hJ hwp
    rw [wp_whileLoop] at hwp
    rw [wp_whileLoop]
    have hcc := hcond as cs hJ
    by_cases hc : acond as = true
    · rw [if_pos hc] at hwp
      have hcct : ccond cs = true := by rw [← hcc]; exact hc
      rw [if_pos hcct]
      have hsucc : wp abody (fun _ _ => True) E as :=
        WP.wp_consequence abody _ _ E (fun _ _ _ => trivial) as hwp
      have hcomb := wp_and_StateT abody _ _ E as hwp (hμ E as hc hsucc)
      have hcb := hbody (fun _ as' => wp (whileLoop acond abody) Q E as' ∧ μ as' < μ as) E cs
        (by simp only [top_meet]; exact ⟨as, hJ, hcomb⟩)
      simp only [relRef_γQ] at hcb
      refine WP.wp_consequence cbody _ _ E ?_ cs hcb
      intro _ cs' hpost'
      obtain ⟨as', hJ', hwp', hlt'⟩ := hpost'
      exact ih as' cs' (Nat.lt_of_lt_of_le hlt' (Nat.lt_succ_iff.mp hlt)) hJ' hwp'
    · have hcf : acond as = false := by simp only [Bool.not_eq_true] at hc; exact hc
      rw [if_neg (by rw [hcf]; simp)] at hwp
      have hccf : ccond cs = false := by rw [← hcc]; exact hcf
      rw [if_neg (by rw [hccf]; simp)]
      simp only [relRef_γQ]
      exact ⟨as, hJ, hwp⟩

/-- Any program corresponds to itself under the identity (`Eq`) relation: `relRef Eq` recovers the
ordinary `wp`, since `γQ id Q` is `Q` up to the existential witness. -/
theorem corres_relEq_self {σ α} (a : StateT σ UB α) :
    Corres (relRef (Eq : σ → σ → Prop)) ⊤ (αVeq (id : α → α)) a a := by
  intro Q E cs hcs
  simp only [top_meet] at hcs
  obtain ⟨as, hJ, hwp⟩ := hcs
  subst hJ
  refine WP.wp_consequence a Q _ E ?_ as hwp
  intro cv cs' hq
  simp only [relRef_γQ]
  exact ⟨cs', rfl, hq⟩
