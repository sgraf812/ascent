import Demo.ZipStruct

/-!
# Register lifting

A program over `MachineData` refines a program over the data memory alone, under
`ofStateRepr MachineData.dmem`. A register read in the concrete program becomes a value of the
abstract program: the hypothesis `PureRefinement (t.regs.get64 r) x True Eq` relates the register
`r` of the state `t` to the abstract value `x`, and the `@[ascend_pure]` rules below abstract a
value computed from registers to the same computation on the abstract values. A step that writes a
register binds the abstract value of the written value to a variable of the abstract program.

The step rules know no instruction. They match the three writes of `Demo.L1`: a load into a
register `loadReg8` becomes `load8` and binds the loaded word, a store `storeWord8` becomes
`store8`, a register write `setReg64` leaves the memory unchanged and adds no abstract step, and an
exit through a mapped word becomes `retAt`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRepr_pred)

namespace Ascent.Kraken

/-! ## Memory steps -/

/-- The eight-byte word at `a`, undefined behaviour when the cell is not mapped. -/
noncomputable def load8 (a : BitVec 64) : BlockM DataMem (BitVec 64) := fun m =>
  UB.guardRet ((Mem.loadInt m a 8).isSome = true) (.ok (BitVec.ofInt 64 (Mem.loadInt m a 8).get!), m)

/-- Store the word `v` at `a`, undefined behaviour unless the cell is mapped and apart from the
return slot at `rsp`. -/
noncomputable def store8 (rsp a v : BitVec 64) : BlockM DataMem Unit :=
  modifyIf (fun m => (Mem.loadInt m a 8).isSome = true ∧ Mem.Blocks.Disjoint [(rsp, 8)] [(a, 8)])
    fun m => Mem.storeInt m a 8 v.toInt

/-- Return through the return slot at `rsp`. -/
noncomputable def retAt {α : Type} (rsp : BitVec 64) : BlockM DataMem α :=
  exitIf (fun m => (Mem.loadInt m rsp 8).isSome = true) id .exit

section
variable (Q : BitVec 64 → DataMem → Prop) (Qu : Unit → DataMem → Prop)
  (E : (CfgLabel → DataMem → Prop) × EStack⟨⟩) (m : DataMem)

theorem wp_load8 (a : BitVec 64) :
    wp (load8 a) Q E m
      = ((Mem.loadInt m a 8).isSome = true ∧ Q (BitVec.ofInt 64 (Mem.loadInt m a 8).get!) m) := by
  rw [wp_BlockM_eq, show (load8 a).run.run m = load8 a m from rfl, load8]
  by_cases h : (Mem.loadInt m a 8).isSome = true
  · rw [UB.guardRet_of_pos h]
    simp only [h, true_and]
    rfl
  · rw [UB.guardRet_of_neg h, UB.fail_eq]
    simp only [Bool.not_eq_true] at h
    simp [h]

theorem wp_store8 (rsp a v : BitVec 64) :
    wp (store8 rsp a v) Qu E m
      = (((Mem.loadInt m a 8).isSome = true ∧ Mem.Blocks.Disjoint [(rsp, 8)] [(a, 8)])
          ∧ Qu () (Mem.storeInt m a 8 v.toInt)) := wp_modifyIf _ _ _ _ _

theorem wp_retAt {α : Type} {Qα : α → DataMem → Prop} (rsp : BitVec 64) :
    wp (retAt rsp : BlockM DataMem α) Qα E m = ((Mem.loadInt m rsp 8).isSome = true ∧ E.1 .exit m) :=
  wp_exitIf _ _ _ _ _

theorem retAt_bind {α β : Type} (rsp : BitVec 64) (k : α → BlockM DataMem β) :
    (retAt rsp >>= k) = retAt rsp :=
  exitIf_bind _ _ _ _

end

/-- `c ≐ x`: the concrete value `c` abstracts to the abstract value `x`. -/
scoped notation:50 c:51 " ≐ " x:51 => PureRefinement c x True Eq

/-! ## Values -/

/-- `RegsRel rs t`: each register `r` of `rs` holds its abstract value `v` in the state `t`. -/
abbrev RegsRel : List (Reg64 × BitVec 64) → MachineData → Prop
  | [], _ => True
  | (r, v) :: rs, t => t.regs.get64 r ≐ v ∧ RegsRel rs t

attribute [vcgen_simp] RegsRel

section
variable {w : Nat} {a b x y : BitVec w} {P₁ P₂ : Prop}

@[ascend_pure] theorem abs_add (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a + b) (x + y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_mul (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a * b) (x * y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_and (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (a &&& b) (x &&& y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_cmp {cc : CondCode} {a b x y : BitVec 64}
    (h₁ : PureRefinement a x P₁ Eq) (h₂ : PureRefinement b y P₂ Eq) :
    PureRefinement (cc.cmp a b) (cc.cmp x y) (P₁ ∧ P₂) Eq := fun ⟨hp₁, hp₂⟩ => by
  rw [h₁ hp₁, h₂ hp₂]

@[ascend_pure] theorem abs_sib8 {t : MachineData} {b i : Reg64} {d : Int64} {x y : BitVec 64}
    (hb : PureRefinement (t.regs.get64 b) x P₁ Eq) (hi : PureRefinement (t.regs.get64 i) y P₂ Eq) :
    PureRefinement (sib8 b i d t) (x + y * 8 + BitVec.ofInt 64 d.toInt) (P₁ ∧ P₂) Eq :=
  fun ⟨hp₁, hp₂⟩ => by rw [sib8, hb hp₁, hi hp₂]

@[ascend_pure low] theorem abs_refl {α : Type} {c : α} : PureRefinement c c True Eq :=
  PureRefinement.of_rel rfl

end

/-! ## Steps -/

attribute [ascend] wrp_bind

section
variable {Q : Unit → BitVec 64 → MachineData → Prop} {Qu : Unit → Unit → MachineData → Prop}
  {E : (CfgLabel → CfgLabel → MachineData → Prop) × EStack⟨⟩}

@[ascend] theorem wrp_pure_unit :
    Qu () () ⊑ wrp (ofStateRepr MachineData.dmem) (pure () : BlockM MachineData Unit)
      (pure () : BlockM DataMem Unit) Qu E :=
  wrp_pure () ()

@[ascend] theorem wrp_loadReg8_load8 (r : Reg64) (a : MachineData → BitVec 64)
    (e : BitVec 64 → MachineData → BitVec 64) (pa : BitVec 64) :
    (fun t => a t ≐ pa ∧
      (loadOk8 a t → ∀ w, word8 (a t) t ≐ w → Q () w (loadReg8 r a e t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (loadOk8 a) (loadReg8 r a e))
          (load8 pa) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_load8] at ht
  obtain ⟨⟨ha, hk⟩, hl, hq⟩ := ht
  have ha : a t = pa := ha trivial
  have hg : loadOk8 a t := by rw [loadOk8, ha]; exact hl
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, _, hk hg _ (PureRefinement.of_rel ?_), hq⟩
  rw [word8, ha]

@[ascend] theorem wrp_storeWord8_store8 (a v : MachineData → BitVec 64) (sp pa pv : BitVec 64) :
    (fun t => t.regs.get64 .rsp ≐ sp ∧ a t ≐ pa ∧ v t ≐ pv ∧
      (storeOk8 a t → Qu () () (storeWord8 a v t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (storeOk8 a) (storeWord8 a v))
          (store8 sp pa pv) Qu E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_store8] at ht
  obtain ⟨⟨hsp, ha, hv, hk⟩, ⟨hl, hd⟩, hq⟩ := ht
  have hsp : t.regs.get64 .rsp = sp := hsp trivial
  have ha : a t = pa := ha trivial
  have hv : v t = pv := hv trivial
  have hg : storeOk8 a t := by rw [storeOk8, loadOk8, ha, hsp]; exact ⟨hl, hd⟩
  rw [wp_modifyIf, Concretization.post_pi]
  refine ⟨hg, (), hk hg, ?_⟩
  simp only [ofStateRepr_pred, storeWord8, ha, hv]
  exact hq

end

/-! ## Control -/

/-- One iteration of two lockstep loops: both continue with the loop values related by `R`, or
both stop with the results related by `Q`. -/
@[reducible] def StepRel {σ βc βa : Type} (R : βc → σ → βa → Prop) (Q : βc → βa → σ → Prop) :
    ForInStep βc → ForInStep βa → σ → Prop
  | .yield c, .yield a, t => R c t a
  | .done c, .done a, t => Q c a t
  | _, _, _ => False

section
variable {σc σa : Type} {view : σc → σa} {E : (CfgLabel → CfgLabel → σc → Prop) × EStack⟨⟩}

theorem wrp_forIn_lockstep {βc βa : Type} (R : βc → σc → βa → Prop) (cinit : βc) (ainit : βa)
    {fc : Unit → βc → BlockM σc (ForInStep βc)} {fa : Unit → βa → BlockM σa (ForInStep βa)}
    {Q : βc → βa → σc → Prop}
    (hbody : ∀ c a, (fun t => R c t a) ⊑
      wrp (ofStateRepr view) (fc () c) (fa () a) (StepRel R Q) E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view) (FixLoop.mk.forIn cinit fc)
      (FixLoop.mk.forIn ainit fa) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  haveI : Nonempty βa := ⟨ainit⟩
  have key := FixLoop.forIn_induct fa
    (fun g => ∀ c a t, R c t a → wp (g a) Qa Ea (view t) →
      wp (FixLoop.mk.forIn c fc) ((ofStateRepr view).post Q Qa)
        (EPostsConcretization.ePosts (ofStateRepr view) E Ea) t)
    (admissible_pi _ fun _ => admissible_pi _ fun a => admissible_pi _ fun t =>
      admissible_pi _ fun _ =>
        admissible_apply (fun _ u => wp u Qa Ea (view t) → _) a
          (admissible_wp_imp _ Ea (view t) _)) ?_
  · exact key cinit ainit t ht.1 ht.2
  intro g ih c a t hR hw
  rw [FixLoop.forIn_eq, WPMonadExact.wp_bind_eq]
  simp only [FixLoop.step, WPMonadExact.wp_bind_eq] at hw
  have hb := wrp_transport (hbody c a)
    (fun r m => match r with | .done a' => Qa a' m | .yield a' => wp (g a') Qa Ea m) Ea t (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]
      refine ⟨hR, WP.wp_monotone_post (x := fa () a) ?_ (view t) hw⟩
      intro r m hr
      cases r <;> simp only [WPMonadExact.wp_pure_eq] at hr ⊢ <;> exact hr)
  refine WP.wp_monotone_post (x := fc () c) ?_ t hb
  intro rc t' h'
  rw [Concretization.post_pi] at h'
  obtain ⟨ra, hrel, hq⟩ := h'
  simp only [ofStateRepr_pred] at hq
  cases rc <;> cases ra <;> simp only [StepRel] at hrel
  · simp only [WPMonadExact.wp_pure_eq]
    rw [Concretization.post_pi]
    exact ⟨_, hrel, hq⟩
  · exact ih _ _ t' hrel hq

theorem wrp_forIn_lockstep_bind_unit {βc βa : Type} (R : βc → σc → βa → Prop) (cinit : βc)
    (ainit : βa) {fc : Unit → βc → BlockM σc (ForInStep βc)}
    {fa : Unit → βa → BlockM σa (ForInStep βa)} {Q : Unit → Unit → σc → Prop}
    (hbody : ∀ c a, (fun t => R c t a) ⊑ wrp (ofStateRepr view) (fc () c) (fa () a)
      (StepRel R fun _ _ t => Q () () t) E) :
    (fun t => R cinit t ainit) ⊑ wrp (ofStateRepr view)
      (FixLoop.mk.forIn cinit fc >>= fun _ => pure ())
      (FixLoop.mk.forIn ainit fa >>= fun _ => pure ()) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq,
    WPMonadExact.wp_pure_eq] at ht
  have h := wrp_transport (wrp_forIn_lockstep R cinit ainit hbody) (fun _ => Qa ()) Ea t
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ht)
  rw [WPMonadExact.wp_bind_eq]
  refine WP.wp_monotone_post (x := FixLoop.mk.forIn cinit fc) ?_ t h
  intro u t' h'
  rw [Concretization.post_pi] at h'
  obtain ⟨_, hq, hqa⟩ := h'
  simp only [WPMonadExact.wp_pure_eq]
  rw [Concretization.post_pi]
  exact ⟨(), hq, hqa⟩

theorem wrp_forIn_diag_bind_unit {β : Type} (I : σc → β → Prop) (init : β)
    {fc : Unit → β → BlockM σc (ForInStep β)} {fa : β → BlockM σa (ForInStep β)}
    {Q : Unit → Unit → σc → Prop}
    (hbody : ∀ v, (fun t => I t v) ⊑ wrp (ofStateRepr view) (fc () v) (fa v)
      (StepRel (fun c t a => c = a ∧ I t a) fun _ _ t => Q () () t) E) :
    (fun t => I t init) ⊑ wrp (ofStateRepr view)
      (FixLoop.mk.forIn init fc >>= fun _ => pure ())
      (FixLoop.mk.forIn init (fun _ v => fa v) >>= fun _ => pure ()) Q E := by
  refine PartialOrder.rel_trans ?_ (wrp_forIn_lockstep_bind_unit
    (fun c t a => c = a ∧ I t a) init init (fa := fun _ v => fa v) fun c a => ?_)
  · exact fun t h => ⟨rfl, h⟩
  · intro t ⟨hca, h⟩
    subst hca
    exact hbody c t h

@[ascend] theorem wrp_pure_same {α : Type} {Q : α → α → σc → Prop} (x : α) :
    Q x x ⊑ wrp (ofStateRepr view) (pure x : BlockM σc α) (pure x : BlockM σa α) Q E :=
  wrp_pure x x

end

section
variable {AV : Type} {Qu : Unit → AV → MachineData → Prop}
  {E : (CfgLabel → CfgLabel → MachineData → Prop) × EStack⟨⟩}

theorem wrp_forIn_lockstep_unit {βa : Type} (R : MachineData → βa → Prop) (ab : βa)
    {fc : Unit → PUnit → BlockM MachineData (ForInStep PUnit)}
    {fa : βa → BlockM DataMem (ForInStep βa)}
    {Q : PUnit → Unit → MachineData → Prop}
    (hbody : ∀ v, (fun t => R t v) ⊑ wrp (ofStateRepr MachineData.dmem) (fc () PUnit.unit) (fa v)
      (StepRel (fun _ t a => R t a) fun u _ t => Q u () t) E) :
    (fun t => R t ab) ⊑ wrp (ofStateRepr MachineData.dmem) (FixLoop.mk.forIn PUnit.unit fc)
      (FixLoop.mk.forIn ab (fun _ v => fa v) >>= fun _ => pure ()) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, WPMonadExact.wp_bind_eq,
    WPMonadExact.wp_pure_eq] at ht
  have h := wrp_transport
    (wrp_forIn_lockstep (fun _ t a => R t a) PUnit.unit ab (fa := fun _ v => fa v)
      (Q := fun u _ t => Q u () t) fun _ v => hbody v) (fun _ => Qa ()) Ea t
    (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ht)
  refine WP.wp_monotone_post (x := FixLoop.mk.forIn PUnit.unit fc) ?_ t h
  intro u t' h'
  rw [Concretization.post_pi] at h' ⊢
  obtain ⟨_, hq, hqa⟩ := h'
  exact ⟨(), hq, hqa⟩

@[ascend] theorem wrp_condState {CV : Type} {Q : CV → AV → MachineData → Prop}
    {c : MachineData → Bool}
    {x y : BlockM MachineData CV} {ax ay : BlockM DataMem AV} (b : Bool) :
    (fun t => c t ≐ b ∧
      (c t = true → wrp (ofStateRepr MachineData.dmem) x ax Q E t) ∧
      (c t = false → wrp (ofStateRepr MachineData.dmem) y ay Q E t))
      ⊑ wrp (ofStateRepr MachineData.dmem) (condState c x y) (if b then ax else ay) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  obtain ⟨⟨hb, hx, hy⟩, hw⟩ := ht
  have hb : c t = b := hb trivial
  rw [wp_condState]
  cases b with
  | true =>
    simp only [hb, ↓reduceIte] at hw ⊢
    exact wrp_transport (P := wrp (ofStateRepr MachineData.dmem) x ax Q E) PartialOrder.rel_refl
      Qa Ea t
      (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hx hb, hw⟩)
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact wrp_transport (P := wrp (ofStateRepr MachineData.dmem) y ay Q E) PartialOrder.rel_refl
      Qa Ea t
      (by simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]; exact ⟨hy hb, hw⟩)

@[ascend high] theorem wrp_stutter_bind {CV : Type} {Q : CV → AV → MachineData → Prop}
    (f : MachineData → MachineData)
    {k : Unit → BlockM MachineData CV} {a : BlockM DataMem AV} (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => wrp (ofStateRepr MachineData.dmem) (k ()) a Q E (f t))
      ⊑ wrp (ofStateRepr MachineData.dmem) (modifyIf (fun _ => True) f >>= k) a Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at ht
  obtain ⟨hk, hw⟩ := ht
  rw [WPMonadExact.wp_bind_eq, wp_modifyIf]
  refine ⟨trivial, wrp_transport (P := wrp (ofStateRepr MachineData.dmem) (k ()) a Q E)
    PartialOrder.rel_refl Qa Ea (f t) ?_⟩
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, hf]
  exact ⟨hk, hw⟩

@[ascend] theorem wrp_exitIf_retAt {CV AV : Type} {Q : CV → AV → MachineData → Prop}
    (a : MachineData → BitVec 64) (f : MachineData → MachineData) (pa : BitVec 64)
    (hf : ∀ t, (f t).dmem = t.dmem) :
    (fun t => a t ≐ pa ∧ (loadOk8 a t → E.1 .exit .exit (f t)))
      ⊑ wrp (ofStateRepr MachineData.dmem) (exitIf (loadOk8 a) f .exit : BlockM MachineData CV)
          (retAt pa : BlockM DataMem AV) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro t ht
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred, wp_retAt] at ht
  obtain ⟨⟨ha, hk⟩, hl, he⟩ := ht
  have ha : a t = pa := ha trivial
  have hg : loadOk8 a t := by rw [loadOk8, ha]; exact hl
  rw [wp_exitIf]
  refine ⟨hg, ?_⟩
  simp only [EPostsConcretization.ePosts_cons]
  rw [Concretization.post_pi]
  refine ⟨.exit, hk hg, ?_⟩
  simp only [ofStateRepr_pred, hf]
  exact he

@[ascend] theorem wrp_yield {βa : Type} {Q : ForInStep PUnit → ForInStep βa → MachineData → Prop}
    (v : βa) :
    (fun t => Q (.yield PUnit.unit) (.yield v) t) ⊑ wrp (ofStateRepr MachineData.dmem)
      (pure (.yield PUnit.unit) : BlockM MachineData (ForInStep PUnit))
      (pure (.yield v) : BlockM DataMem (ForInStep βa)) Q E :=
  wrp_pure (Q := Q) (ForInStep.yield PUnit.unit) (ForInStep.yield v)

end

end Ascent.Kraken
