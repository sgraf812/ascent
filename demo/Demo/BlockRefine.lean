import Demo.L1

/-!
# Refinement of block programs

The rules of a pass whose concrete program is a `BlockM` program: the steps `modifyIf`, `exitIf`
and `branch` under a state representation, and the loop by the loop.

`Refinement.cfgLoop` is fixpoint induction over the abstract `cfgLoop`: to refine it, it suffices
to refine one unfolding `cfgBody` in which the recursive call is an arbitrary block function `g`
that the concrete loop refines. `refines_cfgLoop` is the lockstep instance for two block tables
over the same `next`: the blocks of the concrete table refine the cells of the abstract table at
the same label, a fallthrough and a jump land on a label of the table or on `.exit`, and the
invariant `I` holds at every label.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr

namespace Ascent

/-- The labels of a table. -/
def Table.keys {κ β : Type} (tbl : Table κ β) : List κ := tbl.map Prod.fst

@[simp, vcgen_simp] theorem Table.keys_nil {κ β : Type} : Table.keys ([] : Table κ β) = [] := rfl
@[simp, vcgen_simp] theorem Table.keys_cons {κ β : Type} (e : κ × β) (tbl : Table κ β) :
    Table.keys (e :: tbl) = e.1 :: Table.keys tbl := rfl

theorem Table.get_mem {κ β : Type} [DecidableEq κ] [Inhabited β] {tbl : Table κ β} {k : κ}
    (h : k ∈ Table.keys tbl) : (k, Table.get tbl k) ∈ tbl := by
  induction tbl with
  | nil => simp [Table.keys] at h
  | cons e tbl ih =>
    rcases e with ⟨k', b⟩
    by_cases hk : k' = k
    · subst hk
      simp only [Table.get, List.lookup, beq_self_eq_true, Option.getD_some]
      exact List.mem_cons_self
    · have h' : k ∈ Table.keys tbl := by simpa [Table.keys, Ne.symm hk] using h
      have hb : (k == k') = false := beq_eq_false_iff_ne.mpr (Ne.symm hk)
      have : Table.get ((k', b) :: tbl) k = Table.get tbl k := by
        simp [Table.get, List.lookup, hb]
      rw [this]
      exact List.mem_cons_of_mem _ (ih h')

end Ascent

namespace Ascent.Kraken

section
variable {Aσ : Type} (ablock : CfgLabel → BlockM Aσ Unit) (next : CfgLabel → CfgLabel)

/-- One unfolding of `cfgFix`, with `g` in place of the recursive call. -/
def cfgBody (g : CfgLabel → BlockM Aσ Unit) (l : CfgLabel) (s : Aσ) :
    UB (Except CfgLabel Unit × Aσ) :=
  if l = .exit then pure (.ok (), s) else
    (ablock l).run.run s >>= fun p =>
      match p.1 with
      | .ok _ => (g (next l)).run.run p.2
      | .error l' => if l' = .exit then pure (.error .exit, p.2) else (g l').run.run p.2

/-- The unfolding as a program. -/
def cfgStep (g : CfgLabel → BlockM Aσ Unit) (l : CfgLabel) : BlockM Aσ Unit :=
  cfgBody ablock next g l

/-- A state-passing function as a program. -/
def asBlock (f : Aσ → UB (Except CfgLabel Unit × Aσ)) : BlockM Aσ Unit := f

variable (Qa : Unit → Aσ → Prop) (Ea : (CfgLabel → Aσ → Prop) × EStack⟨⟩)

/-- The exception post of one block under `g`: continue by `g` at a thrown label, `.exit` is final. -/
def bodyEPosts (g : CfgLabel → BlockM Aσ Unit) (l' : CfgLabel) : Aσ → Prop :=
  if l' = .exit then Ea.1 .exit else wp (g l') Qa Ea

theorem wp_cfgBody (g : CfgLabel → BlockM Aσ Unit) (l : CfgLabel) (s : Aσ) :
    wp (cfgStep ablock next g l) Qa Ea s
      = if l = .exit then Qa () s else
          wp (ablock l) (fun _ => wp (g (next l)) Qa Ea) (bodyEPosts Qa Ea g, Ea.2) s := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq]
  have hrun : (cfgStep ablock next g l).run.run s = cfgBody ablock next g l s := rfl
  rw [hrun]
  unfold cfgBody
  split
  · simp only [UB.wp_pure_eq]
    rfl
  · simp only [UB.wp_bind_eq]
    rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq]
    congr 1
    funext p
    rcases p with ⟨r, s'⟩
    rcases r with l' | _
    · by_cases h : l' = .exit
      · subst h
        simp only [eq_self, ↓reduceIte, UB.wp_pure_eq]
        rfl
      · simp only [h, ↓reduceIte]
        show _ = bodyEPosts Qa Ea g l' s'
        simp only [bodyEPosts, h, ↓reduceIte]
        rfl
    · rfl

theorem wp_cfgBody_fn (g : CfgLabel → BlockM Aσ Unit) (l : CfgLabel) :
    wp (cfgStep ablock next g l) Qa Ea
      = if l = .exit then Qa () else
          wp (ablock l) (fun _ => wp (g (next l)) Qa Ea) (bodyEPosts Qa Ea g, Ea.2) := by
  funext s
  rw [wp_cfgBody]
  split <;> rfl

end

/-! ## Steps under a state representation

A concrete step refines an abstract step under `ofStateRepr view` when the abstract guard implies
the concrete guard and the view of the concrete update is the abstract update of the view. -/

section
variable {Cσ Aσ : Type} (view : Cσ → Aσ) {Q : Unit → Unit → Cσ → Prop}
  {E : (CfgLabel → CfgLabel → Cσ → Prop) × EStack⟨⟩}

theorem Concretization.ofStateRepr_pred_iSup (ι : Type) (X : ι → Aσ → Prop) :
    (Concretization.ofStateRepr view).pred (iSup X)
      ⊑ iSup fun i => (Concretization.ofStateRepr view).pred (X i) := by
  intro cs h
  simp only [Concretization.ofStateRepr_pred, iSup_apply, iSup_prop_eq_exists] at h ⊢
  exact h

theorem wrp_pure_unit {γ : Concretization (Cσ → Prop) (Aσ → Prop)} :
    Q () () ⊑ wrp γ (pure () : BlockM Cσ Unit) (pure () : BlockM Aσ Unit) Q E :=
  wrp_pure () ()

theorem wrp_modifyIf_repr {g : Cσ → Prop} {f : Cσ → Cσ} (g' : Aσ → Prop) (f' : Aσ → Aσ)
    (hg : ∀ s, g' (view s) → g s) (hf : ∀ s, g' (view s) → view (f s) = f' (view s)) :
    (fun s => g' (view s) → Q () () (f s))
      ⊑ wrp (Concretization.ofStateRepr view) (modifyIf g f) (modifyIf g' f') Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred, wp_modifyIf] at hs
  obtain ⟨hQ, hg', hQa⟩ := hs
  rw [wp_modifyIf]
  refine ⟨hg s hg', ?_⟩
  rw [Concretization.post_pi]
  exact ⟨(), hQ hg', by simp only [Concretization.ofStateRepr_pred]; rw [hf s hg']; exact hQa⟩

theorem wrp_exitIf_repr {g : Cσ → Prop} {f : Cσ → Cσ} (g' : Aσ → Prop) (f' : Aσ → Aσ)
    (hg : ∀ s, g' (view s) → g s) (hf : ∀ s, g' (view s) → view (f s) = f' (view s))
    (l : CfgLabel) :
    (fun s => g' (view s) → E.1 l l (f s))
      ⊑ wrp (Concretization.ofStateRepr view) (exitIf g f l) (exitIf g' f' l) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred, wp_exitIf] at hs
  obtain ⟨hE, hg', hEa⟩ := hs
  rw [wp_exitIf]
  refine ⟨hg s hg', ?_⟩
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  exact ⟨l, hE hg', by simp only [Concretization.ofStateRepr_pred]; rw [hf s hg']; exact hEa⟩

theorem wrp_branch_repr {c : Cσ → Bool} (c' : Aσ → Bool) (hc : ∀ s, c s = c' (view s))
    (l : CfgLabel) :
    (fun s => (c s = true → E.1 l l s) ∧ (c s = false → Q () () s))
      ⊑ wrp (Concretization.ofStateRepr view) (branch c l) (branch c' l) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, Concretization.ofStateRepr_pred, wp_branch] at hs
  obtain ⟨⟨hjmp, hfall⟩, hw⟩ := hs
  rw [← hc s] at hw
  rw [wp_branch]
  cases h : c s
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    rw [Concretization.post_pi]
    exact ⟨(), hfall h, hw⟩
  · simp only [h, ↓reduceIte] at hw ⊢
    simp only [EPostsConcretization.ePosts_cons]
    rw [Concretization.post_pi]
    exact ⟨l, hjmp h, hw⟩

end

/-! ## The loop by the loop -/

section
variable {Cσ Aσ : Type} {γ : Concretization (Cσ → Prop) (Aσ → Prop)}
  {E : (CfgLabel → CfgLabel → Cσ → Prop) × EStack⟨⟩}

theorem Refinement.cfgLoop_induct
    (hγ : ∀ (ι : Type) (X : ι → Aσ → Prop), γ.pred (iSup X) ⊑ iSup fun i => γ.pred (X i))
    {cblock : CfgLabel → BlockM Cσ Unit} {cnext : CfgLabel → CfgLabel}
    {ablock : CfgLabel → BlockM Aσ Unit} {anext : CfgLabel → CfgLabel}
    {P : CfgLabel → Cσ → Prop} {Q : Unit → Unit → Cσ → Prop}
    (h : ∀ g : CfgLabel → BlockM Aσ Unit,
      (∀ l, ⦃P l⦄ (cfgLoop cblock cnext l) ⪯[γ] (g l) ⦃Q; E⦄) →
      ∀ l, ⦃P l⦄ (cfgLoop cblock cnext l) ⪯[γ] (cfgStep ablock anext g l) ⦃Q; E⦄) :
    ∀ l, ⦃P l⦄ (cfgLoop cblock cnext l) ⪯[γ] (cfgLoop ablock anext l) ⦃Q; E⦄ := by
  refine cfgFix.fixpoint_induct ablock anext
    (fun f => ∀ l, ⦃P l⦄ (cfgLoop cblock cnext l) ⪯[γ] (asBlock (f l)) ⦃Q; E⦄)
    (admissible_pi_apply (fun l a => ⦃P l⦄ (cfgLoop cblock cnext l) ⪯[γ] (asBlock a) ⦃Q; E⦄)
      fun l => Refinement.admissible (AProg := BlockM Aσ Unit) hγ (P l) _ Q E) ?_
  intro f hf
  exact h (fun l => asBlock (f l)) hf

/-- The precondition at a label: the invariant, at a label of the table or at `.exit`. -/
def cfgPre (keys : List CfgLabel) (I : Cσ → Prop) (l : CfgLabel) : Cσ → Prop :=
  fun s => I s ∧ (l = .exit ∨ l ∈ keys)

@[simp, vcgen_simp] theorem cfgPre_apply (keys : List CfgLabel) (I : Cσ → Prop) (l : CfgLabel)
    (s : Cσ) : cfgPre keys I l s = (I s ∧ (l = .exit ∨ l ∈ keys)) := rfl

theorem refines_cfgLoop
    (hγ : ∀ (ι : Type) (X : ι → Aσ → Prop), γ.pred (iSup X) ⊑ iSup fun i => γ.pred (X i))
    (ctbl : Table CfgLabel (BlockM Cσ Unit)) (atbl : Table CfgLabel (BlockM Aσ Unit))
    (next : CfgLabel → CfgLabel) (I : Cσ → Prop)
    (h : ∀ e ∈ ctbl, ∀ t, I t →
      ⦃(· = t)⦄ e.2 ⪯[γ] (Table.get atbl e.1)
        ⦃fun _ _ => cfgPre (Table.keys ctbl) I (next e.1);
          (fun l' l'' s => l' = l'' ∧ cfgPre (Table.keys ctbl) I l' s, estack⟨⟩)⦄)
    {Q : Unit → Unit → Cσ → Prop} {E : (CfgLabel → CfgLabel → Cσ → Prop) × EStack⟨⟩}
    (hQ : ∀ s, I s → Q () () s) (hE : ∀ s, I s → E.1 .exit .exit s) (l : CfgLabel) :
    ⦃cfgPre (Table.keys ctbl) I l⦄ (cfgLoop (Table.get ctbl) next l) ⪯[γ]
      (cfgLoop (Table.get atbl) next l) ⦃Q; E⦄ := by
  obtain ⟨E₁, E₂⟩ := E
  refine Refinement.cfgLoop_induct hγ (P := cfgPre (Table.keys ctbl) I) ?_ l
  intro g hg l
  refine ⟨wrp_intro fun Qa Ea => ?_⟩
  intro s hs
  simp only [meet_apply, meet_prop_eq_and] at hs
  obtain ⟨⟨hI, hl⟩, hw⟩ := hs
  rw [wp_cfgBody_fn] at hw
  by_cases hex : l = .exit
  · subst hex
    simp only [↓reduceIte] at hw
    rw [wp_cfgLoop_exit, Concretization.post_pi]
    exact ⟨(), hQ s hI, hw⟩
  · simp only [hex, ↓reduceIte] at hw
    rw [wp_cfgLoop _ _ _ _ _ hex]
    have hmem : l ∈ Table.keys ctbl := hl.resolve_left hex
    have hb := wrp_transport (h (l, Table.get ctbl l) (Table.get_mem hmem) s hI).le_wrp
      (fun _ => wp (g (next l)) Qa Ea) (bodyEPosts Qa Ea g, Ea.2) s
      (by simp only [meet_apply, meet_prop_eq_and]; exact ⟨trivial, hw⟩)
    refine WP.wp_monotone (x := Table.get ctbl l) ?_ ?_ s hb
    · intro _ s'
      rw [Concretization.post_pi]
      rintro ⟨_, hpre, hg'⟩
      exact wrp_transport (hg (next l)).le_wrp Qa Ea s'
        (by simp only [meet_apply, meet_prop_eq_and]; exact ⟨hpre, hg'⟩)
    · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l' s'
      simp only [EPostsConcretization.ePosts_cons, EPostsConcretization.ePosts_nil]
      rw [Concretization.post_pi]
      rintro ⟨l'', ⟨rfl, hpre⟩, hg'⟩
      by_cases hex' : l' = .exit
      · subst hex'
        simp only [bodyEPosts, ↓reduceIte] at hg'
        simp only [cfgEPosts, ↓reduceIte]
        rw [Concretization.post_pi]
        exact ⟨.exit, hE s' hpre.1, hg'⟩
      · simp only [bodyEPosts, hex', ↓reduceIte] at hg'
        simp only [cfgEPosts, hex', ↓reduceIte]
        exact wrp_transport (hg l').le_wrp Qa Ea s'
          (by simp only [meet_apply, meet_prop_eq_and]; exact ⟨hpre, hg'⟩)
end

/-! ## Total correctness of the loop

`wp_cfgLoop_of_inv` proves a `wp` of `cfgLoop` from an invariant `I` at every label and a variant
`V` that every step to a label other than `.exit` decreases. -/

section
variable {σ : Type} (ablock : CfgLabel → BlockM σ Unit) (next : CfgLabel → CfgLabel)
  (Qa : Unit → σ → Prop) (Ea : (CfgLabel → σ → Prop) × EStack⟨⟩)

theorem wp_cfgLoop_of_inv (I : CfgLabel → σ → Prop) (V : CfgLabel → σ → Nat)
    (hexit : ∀ s, I .exit s → Qa () s)
    (hstep : ∀ l s, l ≠ .exit → I l s →
      wp (ablock l)
        (fun _ s' => I (next l) s' ∧ (next l ≠ .exit → V (next l) s' < V l s))
        (fun l' s' => if l' = .exit then Ea.1 .exit s' else I l' s' ∧ V l' s' < V l s, Ea.2) s) :
    ∀ l s, I l s → wp (cfgLoop ablock next l) Qa Ea s := by
  intro l s
  induction h : V l s using Nat.strongRecOn generalizing l s with
  | _ v ih =>
    intro hI
    by_cases hl : l = .exit
    · subst hl
      rw [wp_cfgLoop_exit]
      exact hexit s hI
    · rw [wp_cfgLoop _ _ _ _ _ hl]
      refine WP.wp_monotone (x := ablock l) ?_ ?_ s (hstep l s hl hI)
      · rintro _ s' ⟨hI', hV⟩
        by_cases hn : next l = .exit
        · rw [hn] at hI' ⊢
          rw [wp_cfgLoop_exit]
          exact hexit s' hI'
        · exact ih _ (h ▸ hV hn) (next l) s' rfl hI'
      · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
        intro l' s' h'
        by_cases hx : l' = .exit
        · subst hx
          simp only [↓reduceIte] at h'
          simp only [cfgEPosts, ↓reduceIte]
          exact h'
        · simp only [hx, ↓reduceIte] at h'
          simp only [cfgEPosts, hx, ↓reduceIte]
          exact ih _ (h ▸ h'.2) l' s' rfl h'.1

end

end Ascent.Kraken
