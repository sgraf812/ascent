import AscentTests.Loop

/-!
# A general while-loop correspondence

The loop body mutates the loop counter, so a *fixed* state coupling cannot span the loop. The
correspondence is therefore stated against a **relational** refinement `relRef J`, where
`J : Aσ → Cσ → Prop` couples an abstract and a concrete state (e.g. "the abstract counter equals the
concrete local `i`, and the heaps agree"). The relation is invariant across iterations even though
the coupled *values* change.

`corres_whileLoop` reduces a loop correspondence to: the guards agree under `J`, the body
corresponds (preserving `J`), and the body strictly decreases an abstract variant `μ`. It is proved
by strong induction on `μ`, unfolding both loops one step at a time.
-/

open Std.Internal.Do Lean.Order Ascent

set_option mvcgen.warning false

/-- A refinement from a state relation `J`: an abstract assertion `P` concretizes to "there is a
`J`-related abstract state on which `P` holds". `Zip.l2Ref couples` is the special case
`J as cs := as = cs.heap ∧ couples cs.locals`. -/
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

/-- A relational refinement transports `pure`/`bind`: `ofWPMorphism` needs only the abstract
monad's (`StateT Aσ UB`) `wp` facts, which hold regardless of `J`. -/
instance {Aσ Cσ : Type} (J : Aσ → Cσ → Prop) :
    LawfulRefinement (relRef J) (StateT Cσ UB) (StateT Aσ UB) where
  wp_pure_le := fun _ _ _ => PartialOrder.rel_refl
  wp_bind_le := fun x f post E => by
    intro s; exact UB.wp_bind_le (x s) (fun p => f p.1 p.2) (fun p => post p.1 p.2) E

/-! ## `wp` of `StateT σ UB` constructs, pointwise -/

theorem wp_bind_StateT {σ α β} (x : StateT σ UB α) (f : α → StateT σ UB β)
    (Q : β → σ → Prop) (E : EPost.Nil) (s : σ) :
    wp (x >>= f) Q E s = wp x (fun a s' => wp (f a) Q E s') E s := by
  simp only [StateT.wp_apply_eq, StateT.run_bind, UB.wp_bind_eq]

theorem wp_and_StateT {σ α} (x : StateT σ UB α) (P R : α → σ → Prop) (E : EPost.Nil) (s : σ)
    (hP : wp x P E s) (hR : wp x R E s) : wp x (fun a s' => P a s' ∧ R a s') E s := by
  rw [StateT.wp_apply_eq] at hP hR ⊢
  exact UB.wp_and (x.run s) (fun p => P p.1 p.2) (fun p => R p.1 p.2) E hP hR

/-- One-step unfolding of `whileLoop`'s `wp`. -/
theorem wp_whileLoop {σ} (cond : σ → Bool) (body : StateT σ UB Unit)
    (Q : Unit → σ → Prop) (E : EPost.Nil) (s : σ) :
    wp (whileLoop cond body) Q E s
      = if cond s then wp body (fun _ s' => wp (whileLoop cond body) Q E s') E s else Q () s := by
  rw [whileLoop, StateT.wp_apply_eq, StateT.run, loopFix]
  simp only [wp_ite, UB.wp_bind_eq, UB.wp_pure_eq, StateT.wp_apply_eq, StateT.run]

/-! ## The loop correspondence -/

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

/-! ## Sanity checks -/

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

/-- A terminating countdown loop corresponds to itself: the guards agree, the body corresponds to
itself, and the body strictly decreases the counter (used as the variant). -/
example : Corres (relRef (Eq : Nat → Nat → Prop)) ⊤ (αVeq (id : Unit → Unit))
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1)))
    (whileLoop (fun n => decide (0 < n)) (fun n => pure ((), n - 1))) := by
  apply corres_whileLoop (μ := id)
  · intro as cs h; subst h; rfl
  · exact corres_relEq_self _
  · intro E as h _
    simp only [StateT.wp_apply_eq, StateT.run, UB.wp_pure_eq, id]
    have : 0 < as := by simpa using h
    omega
