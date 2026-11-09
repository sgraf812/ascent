import Ascent.Table
import Ascent.FixLoop
import Ascent.Refinement.Lockstep

/-!
# Block loops

A block program runs in `ExceptT κ (StateT σ UB)`, and a jump to a label `l` is the exception `l`.
`cfgLoop T l` runs the blocks of the table `T`: at a label `l` with a block `b` it runs `b`, a jump
of `b` continues the loop at its target, and a normal end of `b` ends the loop. At a label without
a block the loop leaves by throwing that label, so the targets outside `T` are the exits of the loop.

`cfgLoop_header` makes a label `h` with block `b` the header of a loop over the remaining blocks:
running from `h` is a `repeat'` loop. An iteration runs `b` and then the loop over `T.erase h`;
leaving that loop at `h` continues the iteration, leaving it at any other label leaves the `repeat'`
loop. Applied at every label, the equation turns a table into nested `repeat'` loops. It is Bekić's
elimination of one variable from a system of fixpoint equations.

`ThrowsOnly P x` is the exception effect of `x`: every label that `x` throws satisfies `P`. It has one
rule for each program form, and the rule for a loop asks the effect of the loop body. A header
handler `fun l' => if l' = h then y else throw l'` crosses a loop whose effect excludes `h`
(`tryCatch_forIn_bind`).
-/

open Std.WP Lean.Order

namespace Ascent

namespace BlockLoop

section
variable {κ σ α : Type}

theorem some_bind {α β : Type} (a : α) (f : α → UB β) : (Bind.bind (m := UB) (some a) f) = f a := rfl

theorem wp_run_eq (x : ExceptT κ (StateT σ UB) α) (Q : α → σ → Prop)
    (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp x Q E s = match x.run.run s with
      | none => False
      | some (.ok a, s') => Q a s'
      | some (.error e, s') => E.1 e s' := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq]
  rcases x.run.run s with _ | ⟨l' | a, s'⟩
  · exact bot_prop_eq
  · rfl
  · rfl

theorem wp_throw (l : κ) (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (throw l : ExceptT κ (StateT σ UB) α) Q E s = E.1 l s := by
  rw [wp_run_eq]
  rfl

theorem wp_tryCatch (x : ExceptT κ (StateT σ UB) α) (h : κ → ExceptT κ (StateT σ UB) α)
    (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (tryCatch x h) Q E s = wp x Q (fun l => wp (h l) Q E, E.2) s := by
  rw [wp_run_eq, wp_run_eq]
  show (match (ExceptT.tryCatch x h).run.run s with
    | none => False | some (.ok a, st') => Q a st' | some (.error e, st') => E.1 e st') = _
  simp only [ExceptT.tryCatch, ExceptT.run_mk, StateT.run_bind]
  rw [show StateT.run x s = x.run.run s from rfl]
  rcases x.run.run s with _ | ⟨l | a, s'⟩
  · rfl
  · simp only [some_bind]
    rw [wp_run_eq]
    rfl
  · rfl

theorem ext_wp {x y : ExceptT κ (StateT σ UB) α}
    (h : ∀ (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) s, wp x Q E s → wp y Q E s)
    (h' : ∀ (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) s, wp y Q E s → wp x Q E s) :
    x = y := by
  have key : ∀ (u v : ExceptT κ (StateT σ UB) α) s,
      (∀ (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩), wp u Q E s → wp v Q E s) →
      ∀ r, u.run.run s = some r → v.run.run s = some r := by
    intro u v s huv r hr
    have := huv (fun a st => (some (.ok a, st) : UB _) = some r)
      (fun e st => (some (.error e, st) : UB _) = some r, estack⟨⟩)
    rw [wp_run_eq, wp_run_eq, hr] at this
    rcases r with ⟨_ | _, _⟩ <;>
    · specialize this rfl
      revert this
      rcases v.run.run s with _ | ⟨_ | _, _⟩ <;> simp <;> rintro rfl rfl <;> rfl
  apply ExceptT.ext
  apply StateT.ext
  intro s
  show x.run.run s = y.run.run s
  rcases hx : x.run.run s with _ | r
  · rcases hy : y.run.run s with _ | r
    · rfl
    · rw [key y x s (fun Q E => h' Q E s) r hy] at hx
      exact (nomatch hx)
  · exact (key x y s (fun Q E => h Q E s) r hx).symm

theorem tryCatch_throw (l : κ) (h : κ → ExceptT κ (StateT σ UB) α) :
    tryCatch (throw l : ExceptT κ (StateT σ UB) α) h = h l := by
  apply ext_wp <;> intro Q E s <;> rw [wp_tryCatch, wp_throw] <;> exact id

theorem throw_bind {β : Type} (l : κ) (k : α → ExceptT κ (StateT σ UB) β) :
    ((throw l : ExceptT κ (StateT σ UB) α) >>= k) = throw l := by
  apply ext_wp <;> intro Q E s <;> rw [WPMonadExact.wp_bind_eq, wp_throw, wp_throw] <;> exact id

end

end BlockLoop

open BlockLoop

section
variable {κ σ : Type} [DecidableEq κ]

/-- The fixpoint, at the state-passing type that carries the `CCPO`. -/
def cfgFix (T : Table κ (ExceptT κ (StateT σ UB) Unit)) (l : κ) (s : σ) :
    UB (Except κ Unit × σ) :=
  match T.get? l with
  | none => pure (.error l, s)
  | some b => b.run.run s >>= fun p =>
    match p.1 with
    | .ok _ => pure (.ok (), p.2)
    | .error l' => cfgFix T l' p.2
partial_fixpoint

def cfgLoop (T : Table κ (ExceptT κ (StateT σ UB) Unit)) (l : κ) : ExceptT κ (StateT σ UB) Unit :=
  cfgFix T l

variable (T : Table κ (ExceptT κ (StateT σ UB) Unit))

def cfgStep (f : κ → ExceptT κ (StateT σ UB) Unit) (l : κ) : ExceptT κ (StateT σ UB) Unit :=
  show σ → UB (Except κ Unit × σ) from fun s =>
    match T.get? l with
    | none => pure (.error l, s)
    | some b => b.run.run s >>= fun p =>
      match p.1 with
      | .ok _ => pure (.ok (), p.2)
      | .error l' => (f l').run.run p.2

theorem cfgLoop_eq_cfgStep : cfgLoop T = cfgStep T (cfgLoop T) := by
  funext l
  show (cfgFix T l : σ → UB (Except κ Unit × σ)) = cfgStep T _ l
  funext s
  rw [cfgFix]
  rfl

theorem cfgLoop_induct (motive : (κ → ExceptT κ (StateT σ UB) Unit) → Prop) (hadm : admissible motive)
    (h : ∀ f, motive f → motive (cfgStep T f)) : motive (cfgLoop T) :=
  cfgFix.fixpoint_induct T motive hadm h

theorem cfgLoop_run (l : κ) (s : σ) : (cfgLoop T l).run.run s = cfgFix T l s := rfl

section
variable (f : κ → ExceptT κ (StateT σ UB) Unit) {l : κ} (Q : Unit → σ → Prop)
  (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ)

theorem cfgStep_run_none (hl : T.get? l = none) : (cfgStep T f l).run.run s = pure (.error l, s) := by
  simp only [cfgStep, ExceptT.run, StateT.run, hl]

theorem cfgStep_run_some {b : ExceptT κ (StateT σ UB) Unit} (hl : T.get? l = some b) :
    (cfgStep T f l).run.run s = (b.run.run s >>= fun p =>
      match p.1 with
      | .ok _ => pure (.ok (), p.2)
      | .error l' => (f l').run.run p.2) := by
  simp only [cfgStep, ExceptT.run, StateT.run, hl]

theorem wp_cfgStep_none (hl : T.get? l = none) : wp (cfgStep T f l) Q E s = E.1 l s := by
  rw [wp_run_eq, cfgStep_run_none _ _ _ hl]
  rfl

theorem wp_cfgStep_some {b : ExceptT κ (StateT σ UB) Unit} (hl : T.get? l = some b) :
    wp (cfgStep T f l) Q E s = wp b Q (fun l' => wp (f l') Q E, E.2) s := by
  rw [wp_run_eq, wp_run_eq b, cfgStep_run_some _ _ _ hl]
  rcases b.run.run s with _ | ⟨l' | ⟨⟩, s'⟩
  · rfl
  · simp only [some_bind]
    rw [wp_run_eq]
  · rfl

end

section
variable {l : κ} (Q : Unit → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ)

theorem wp_cfgLoop_none (hl : T.get? l = none) : wp (cfgLoop T l) Q E s = E.1 l s := by
  rw [congrFun (cfgLoop_eq_cfgStep T) l, wp_cfgStep_none _ _ _ _ _ hl]

theorem wp_cfgLoop_some {b : ExceptT κ (StateT σ UB) Unit} (hl : T.get? l = some b) :
    wp (cfgLoop T l) Q E s = wp b Q (fun l' => wp (cfgLoop T l') Q E, E.2) s := by
  rw [congrFun (cfgLoop_eq_cfgStep T) l, wp_cfgStep_some _ _ _ _ _ hl]

end

theorem cfgLoop_none {l : κ} (hl : T.get? l = none) : cfgLoop T l = throw l := by
  apply ext_wp <;> intro Q E s <;> rw [wp_cfgLoop_none _ _ _ _ hl, wp_throw] <;> exact id

theorem cfgLoop_some {l : κ} {b : ExceptT κ (StateT σ UB) Unit} (hl : T.get? l = some b) :
    cfgLoop T l = tryCatch b (cfgLoop T) := by
  apply ext_wp <;> intro Q E s <;> rw [wp_cfgLoop_some _ _ _ _ hl, wp_tryCatch] <;> exact id

omit [DecidableEq κ] in
theorem admissible_wp_imp_fn (P : κ → (Unit → σ → Prop) → ((κ → σ → Prop) × EStack⟨⟩) → σ → Prop) :
    admissible fun f : κ → ExceptT κ (StateT σ UB) Unit =>
      ∀ l Q E s, wp (f l) Q E s → P l Q E s :=
  admissible_pi _ fun l => admissible_pi _ fun Q => admissible_pi _ fun E => admissible_pi _ fun s =>
    admissible_apply (fun _ u => wp u Q E s → P l Q E s) l (admissible_wp_imp _ E s _)

/-! ## Label elimination -/

theorem wp_header_body (h : κ) (b : ExceptT κ (StateT σ UB) Unit) (R : ForInStep PUnit → σ → Prop)
    (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (tryCatch (tryCatch b (cfgLoop (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
        (fun l' => if l' = h then pure (ForInStep.yield PUnit.unit) else throw l')) R E s
      = wp b (fun _ => R (.done PUnit.unit))
          (fun l' => wp (cfgLoop (T.erase h) l') (fun _ => R (.done PUnit.unit))
            (fun l'' => if l'' = h then R (.yield PUnit.unit) else E.1 l'', E.2), E.2) s := by
  have hH : (fun l' => wp ((if l' = h then pure (ForInStep.yield PUnit.unit) else throw l' :
      ExceptT κ (StateT σ UB) (ForInStep PUnit))) R E)
      = fun l' => if l' = h then R (.yield PUnit.unit) else E.1 l' := by
    funext l' t
    split
    · simp only [WPMonadExact.wp_pure_eq]
    · exact wp_throw _ _ _ _
  rw [wp_tryCatch, hH, WPMonadExact.wp_bind_eq]
  simp only [WPMonadExact.wp_pure_eq]
  rw [wp_tryCatch]

theorem unit_post (Q : Unit → σ → Prop) : (fun _ : Unit => Q ()) = Q := funext fun u => by cases u; rfl

section
variable {h : κ} {b : ExceptT κ (StateT σ UB) Unit} (hb : T.get? h = some b)
include hb

theorem wp_cfgLoop_imp_forIn (Q : Unit → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (cfgLoop T h) Q E s → wp (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then pure (ForInStep.yield PUnit.unit) else throw l'))) Q E s := by
  let loop := FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then pure (ForInStep.yield PUnit.unit) else throw l'))
  let H : κ → ExceptT κ (StateT σ UB) Unit := fun l' => if l' = h then loop else throw l'
  have hH : ∀ (Q : Unit → σ → Prop) E, (fun l'' => wp (H l'') Q E)
      = fun l'' => if l'' = h then wp loop Q E else E.1 l'' := by
    intro Q E
    funext l'' t
    simp only [H]
    split
    · rfl
    · exact wp_throw _ _ _ _
  have hnone : (T.erase h).get? h = none := by simp only [Table.get?_erase, ↓reduceIte]
  have hloop : ∀ (Q : Unit → σ → Prop) E s,
      wp loop Q E s = wp b (fun _ => Q ()) (fun l' => wp (cfgLoop (T.erase h) l') (fun _ => Q ())
        (fun l'' => if l'' = h then wp loop Q E else E.1 l'', E.2), E.2) s := by
    intro Q E s
    show wp (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then pure (ForInStep.yield PUnit.unit) else throw l'))) Q E s = _
    refine (congrFun (FixLoop.wp_forIn_eq _ _ _ Q E) s).trans ?_
    rw [wp_header_body]
  have key := cfgLoop_induct T
    (fun f => ∀ l Q E s, wp (f l) Q E s → wp (tryCatch (cfgLoop (T.erase h) l) H) Q E s)
    (admissible_wp_imp_fn _)
  refine fun hw => ?_
  have hR := (key ?_) h Q E s hw
  · rw [wp_tryCatch, wp_cfgLoop_none _ _ _ _ hnone, hH] at hR
    simpa only [↓reduceIte] using hR
  intro f ih l Q E s hw
  rw [wp_tryCatch, hH]
  cases hl : T.get? l with
  | none =>
    have hne : l ≠ h := fun he => by rw [he, hb] at hl; exact nomatch hl
    rw [wp_cfgStep_none _ _ _ _ _ hl] at hw
    have hl' : (T.erase h).get? l = none := by simp only [Table.get?_erase, hne, hl, ↓reduceIte]
    rw [wp_cfgLoop_none _ _ _ _ hl']
    simpa only [hne, ↓reduceIte] using hw
  | some b' =>
    rw [wp_cfgStep_some _ _ _ _ _ hl] at hw
    by_cases hlh : l = h
    · subst hlh
      rw [hb] at hl
      obtain rfl := Option.some.inj hl
      rw [wp_cfgLoop_none _ _ _ _ hnone]
      simp only [↓reduceIte]
      rw [hloop, unit_post]
      refine WP.wp_monotone (x := b) (fun _ _ ht => ht) ?_ s hw
      refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l' t ht
      have := ih l' Q E t ht
      rw [wp_tryCatch, hH] at this
      exact this
    · have hl' : (T.erase h).get? l = some b' := by simp only [Table.get?_erase, hlh, hl, ↓reduceIte]
      rw [wp_cfgLoop_some _ _ _ _ hl']
      refine WP.wp_monotone (x := b') (fun _ _ ht => ht) ?_ s hw
      refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l' t ht
      have := ih l' Q E t ht
      rw [wp_tryCatch, hH] at this
      exact this

theorem wp_forIn_imp_cfgLoop (Q : Unit → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then pure (ForInStep.yield PUnit.unit) else throw l'))) Q E s →
      wp (cfgLoop T h) Q E s := by
  have inner : ∀ (g : PUnit → ExceptT κ (StateT σ UB) PUnit),
      (∀ (Q : Unit → σ → Prop) E s, wp (g PUnit.unit) Q E s → wp (cfgLoop T h) Q E s) →
      ∀ (Q : Unit → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) l s,
        wp (cfgLoop (T.erase h) l) Q
          (fun l'' => if l'' = h then wp (g PUnit.unit) Q E else E.1 l'', E.2) s →
        wp (cfgLoop T l) Q E s := by
    intro g hg Q E
    let E' : (κ → σ → Prop) × EStack⟨⟩ :=
      (fun l'' => if l'' = h then wp (g PUnit.unit) Q E else E.1 l'', E.2)
    have := cfgLoop_induct (T.erase h)
      (fun f => ∀ l s, wp (f l) Q E' s → wp (cfgLoop T l) Q E s)
      (admissible_pi _ fun l => admissible_pi _ fun s =>
        admissible_apply (fun _ u => wp u Q E' s → _) l (admissible_wp_imp _ E' s _))
    refine this ?_
    intro f ih l s hw
    cases hl : (T.erase h).get? l with
    | none =>
      rw [wp_cfgStep_none _ _ _ _ _ hl] at hw
      by_cases hlh : l = h
      · subst hlh
        simp only [E', ↓reduceIte] at hw
        exact hg Q E s hw
      · simp only [E', hlh, ↓reduceIte] at hw
        have hT : T.get? l = none := by simpa only [Table.get?_erase, hlh, ↓reduceIte] using hl
        rw [wp_cfgLoop_none _ _ _ _ hT]
        exact hw
    | some b' =>
      have hlh : l ≠ h := fun he => by simp only [he, Table.get?_erase, ↓reduceIte] at hl; exact nomatch hl
      have hT : T.get? l = some b' := by simpa only [Table.get?_erase, hlh, ↓reduceIte] using hl
      rw [wp_cfgStep_some _ _ _ _ _ hl] at hw
      rw [wp_cfgLoop_some _ _ _ _ hT]
      refine WP.wp_monotone (x := b') (fun _ _ ht => ht) ?_ s hw
      refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l' t ht
      exact ih l' t ht
  have := FixLoop.forIn_induct (m := ExceptT κ (StateT σ UB)) (β := PUnit) (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then pure (ForInStep.yield PUnit.unit) else throw l'))
    (fun g => ∀ (Q : Unit → σ → Prop) E s, wp (g PUnit.unit) Q E s → wp (cfgLoop T h) Q E s)
    (admissible_pi _ fun Q => admissible_pi _ fun E => admissible_pi _ fun s =>
      admissible_apply (fun _ u => wp u Q E s → _) PUnit.unit (admissible_wp_imp _ E s _))
  refine this ?_ Q E s
  intro g ih Q E s hw
  rw [FixLoop.step, WPMonadExact.wp_bind_eq, wp_header_body] at hw
  simp only [WPMonadExact.wp_pure_eq] at hw
  rw [wp_cfgLoop_some _ _ _ _ hb]
  rw [← unit_post Q]
  refine WP.wp_monotone (x := b) (fun _ _ ht => ht) ?_ s hw
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro l' t ht
  rw [unit_post]
  rw [unit_post] at ht
  exact inner g ih Q E l' t ht

theorem cfgLoop_header_of_some : cfgLoop T h = FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
        (fun l' => if l' = h then pure (ForInStep.yield PUnit.unit) else throw l')) :=
  ext_wp (wp_cfgLoop_imp_forIn T hb) (wp_forIn_imp_cfgLoop T hb)

end

theorem cfgLoop_header {h : κ} (hb : (T.get? h).isSome = true) :
    cfgLoop T h = FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch ((T.get? h).getD (throw h)) (cfgLoop (T.erase h)) >>= fun _ =>
          pure (ForInStep.done PUnit.unit))
        (fun l' => if l' = h then pure (ForInStep.yield PUnit.unit) else throw l')) := by
  obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp hb
  rw [hb']
  exact cfgLoop_header_of_some T hb'

theorem cfgLoop_eq_throw {l : κ} (hl : T.get? l = none) : cfgLoop T l = throw l := cfgLoop_none T hl

/-! ## The exception effect of a program -/

/-- `x` throws only labels that satisfy `P`. -/
def ThrowsOnly {α : Type} (P : κ → Prop) (x : ExceptT κ (StateT σ UB) α) : Prop :=
  ∀ (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) s,
    wp x Q E s → wp x Q (fun l t => P l ∧ E.1 l t, E.2) s

section
variable {α β : Type} {P : κ → Prop}

omit [DecidableEq κ] in
theorem ThrowsOnly.pure (a : α) : ThrowsOnly P (pure a : ExceptT κ (StateT σ UB) α) = True := eq_true <| by
  intro Q E s hw
  simpa only [WPMonadExact.wp_pure_eq] using hw

omit [DecidableEq κ] in
theorem ThrowsOnly.throw {l : κ} (hl : P l) :
    ThrowsOnly P (throw l : ExceptT κ (StateT σ UB) α) = True := eq_true <| by
  intro Q E s hw
  rw [wp_throw] at hw ⊢
  exact ⟨hl, hw⟩

omit [DecidableEq κ] in
theorem ThrowsOnly.bind {x : ExceptT κ (StateT σ UB) α} {k : α → ExceptT κ (StateT σ UB) β}
    (hx : ThrowsOnly P x) (hk : ∀ a, ThrowsOnly P (k a)) : ThrowsOnly P (x >>= k) = True := eq_true <| by
  intro Q E s hw
  rw [WPMonadExact.wp_bind_eq] at hw ⊢
  exact WP.wp_monotone (x := x) (fun a t ht => hk a Q E t ht) PartialOrder.rel_refl s
    (hx _ _ s hw)

omit [DecidableEq κ] in
theorem ThrowsOnly.map {x : ExceptT κ (StateT σ UB) α} (f : α → β) (hx : ThrowsOnly P x) :
    ThrowsOnly P (f <$> x) = True := eq_true <| by
  rw [map_eq_pure_bind]
  exact of_eq_true (ThrowsOnly.bind hx fun _ => of_eq_true (ThrowsOnly.pure _))

omit [DecidableEq κ] in
theorem ThrowsOnly.forIn {b : α} {f : Unit → α → ExceptT κ (StateT σ UB) (ForInStep α)}
    (hf : ∀ u v, ThrowsOnly P (f u v)) : ThrowsOnly P (FixLoop.mk.forIn b f) = True := eq_true <| by
  haveI : Nonempty α := ⟨b⟩
  have := FixLoop.forIn_induct (m := ExceptT κ (StateT σ UB)) f
    (fun g => ∀ v (Q : α → σ → Prop) E s, wp (g v) Q E s →
      wp (FixLoop.mk.forIn v f) Q (fun l t => P l ∧ E.1 l t, E.2) s)
    (admissible_pi _ fun v => admissible_pi _ fun Q => admissible_pi _ fun E => admissible_pi _ fun s =>
      admissible_apply (fun _ u => wp u Q E s → _) v (admissible_wp_imp _ E s _))
  refine fun Q E s hw => this ?_ b Q E s hw
  intro g ih v Q E s hw
  rw [FixLoop.step, WPMonadExact.wp_bind_eq] at hw
  rw [FixLoop.wp_forIn_eq]
  refine WP.wp_monotone (x := f () v) ?_ PartialOrder.rel_refl s (hf () v _ _ s hw)
  intro r t ht
  cases r with
  | done v' => simpa only [WPMonadExact.wp_pure_eq] using ht
  | yield v' => exact ih v' Q E t ht

end

/-- A label whose iteration never returns to it runs its block once: the loop at `h` is the
block followed by the loop over the other labels. -/
theorem cfgLoop_eq_tryCatch {h : κ} (hb : (T.get? h).isSome = true)
    (hn : ThrowsOnly (· ≠ h)
      (tryCatch ((T.get? h).getD (throw h)) (fun l' => cfgLoop (T.erase h) l'))) :
    cfgLoop T h = tryCatch ((T.get? h).getD (throw h)) (fun l' => cfgLoop (T.erase h) l') := by
  obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp hb
  rw [hb'] at hn ⊢
  simp only [Option.getD_some] at hn ⊢
  let X := tryCatch b (fun l' => cfgLoop (T.erase h) l')
  have hloop : ∀ (Q : Unit → σ → Prop) E s,
      wp (cfgLoop T h) Q E s = wp X Q (fun l => if l = h then wp (cfgLoop T h) Q E else E.1 l, E.2) s := by
    intro Q E s
    rw [cfgLoop_header_of_some T hb']
    refine (congrFun (FixLoop.wp_forIn_eq _ _ _ Q E) s).trans ?_
    rw [wp_header_body, wp_tryCatch, unit_post]
  apply ext_wp
  · intro Q E s hw
    rw [hloop] at hw
    refine WP.wp_monotone (x := X) (fun _ _ ht => ht) ?_ s (hn _ _ s hw)
    refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l t ⟨hl, ht⟩
    simpa only [hl, ↓reduceIte] using ht
  · intro Q E s hw
    rw [hloop]
    refine WP.wp_monotone (x := X) (fun _ _ ht => ht) ?_ s (hn _ _ s hw)
    refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
    intro l t ⟨hl, ht⟩
    simpa only [hl, ↓reduceIte] using ht

/-- A handler that catches only `h` crosses a loop that never throws `h`. -/
theorem tryCatch_forIn_bind {β γ : Type} {h : κ} {i : β} {f : Unit → β → ExceptT κ (StateT σ UB) (ForInStep β)}
    {k : β → ExceptT κ (StateT σ UB) γ} {y : ExceptT κ (StateT σ UB) γ}
    (hf : ThrowsOnly (· ≠ h) (FixLoop.mk.forIn i f)) :
    tryCatch (FixLoop.mk.forIn i f >>= k) (fun l' => if l' = h then y else throw l')
      = FixLoop.mk.forIn i f >>= fun r => tryCatch (k r) (fun l' => if l' = h then y else throw l') := by
  have hE : ∀ (Q : γ → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) l t, l ≠ h →
      (wp (if l = h then y else throw l) Q E t ↔ E.1 l t) := by
    intro Q E l t hl
    simp only [hl, ↓reduceIte, wp_throw]
  apply ext_wp
  · intro Q E s hw
    rw [wp_tryCatch, WPMonadExact.wp_bind_eq] at hw
    rw [WPMonadExact.wp_bind_eq]
    refine WP.wp_monotone (x := FixLoop.mk.forIn i f) (fun r t ht => ?_) ?_ s (hf _ _ s hw)
    · rw [wp_tryCatch]; exact ht
    · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l t ⟨hl, ht⟩
      exact (hE Q E l t hl).mp ht
  · intro Q E s hw
    rw [WPMonadExact.wp_bind_eq] at hw
    rw [wp_tryCatch, WPMonadExact.wp_bind_eq]
    refine WP.wp_monotone (x := FixLoop.mk.forIn i f) (fun r t ht => ?_) ?_ s (hf _ _ s hw)
    · rw [wp_tryCatch] at ht; exact ht
    · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l t ⟨hl, ht⟩
      exact (hE Q E l t hl).mpr ht

theorem tryCatch_map_forIn {β γ : Type} {h : κ} {i : β}
    {f : Unit → β → ExceptT κ (StateT σ UB) (ForInStep β)} {g : β → γ} {y : ExceptT κ (StateT σ UB) γ}
    (hf : ThrowsOnly (· ≠ h) (FixLoop.mk.forIn i f)) :
    tryCatch (g <$> FixLoop.mk.forIn i f) (fun l' => if l' = h then y else throw l')
      = g <$> FixLoop.mk.forIn i f := by
  have hp : ∀ r : β, tryCatch (pure (g r) : ExceptT κ (StateT σ UB) γ)
      (fun l' => if l' = h then y else throw l') = pure (g r) := fun r => by
    apply ext_wp <;> intro Q E s <;> rw [wp_tryCatch] <;>
      simp only [WPMonadExact.wp_pure_eq] <;> exact id
  have := tryCatch_forIn_bind (k := fun r => pure (g r)) (y := y) hf
  simp only [hp] at this
  simpa only [map_eq_pure_bind] using this

theorem tryCatch_forIn {β : Type} {h : κ} {i : β} {f : Unit → β → ExceptT κ (StateT σ UB) (ForInStep β)}
    {y : ExceptT κ (StateT σ UB) β} (hf : ThrowsOnly (· ≠ h) (FixLoop.mk.forIn i f)) :
    tryCatch (FixLoop.mk.forIn i f) (fun l' => if l' = h then y else throw l') = FixLoop.mk.forIn i f := by
  simpa only [id_map] using tryCatch_map_forIn (g := id) (y := y) hf

/-! ## The number of blocks a run executes -/

def count : Nat → κ → σ → UB Nat
  | 0, _, _ => UB.fail
  | n + 1, l, st =>
    match T.get? l with
    | none => pure 0
    | some b => b.run.run st >>= fun p =>
      match p.1 with
      | .ok _ => pure 1
      | .error l' => (· + 1) <$> count n l' p.2

theorem count_of_cfgFix : ∀ (l : κ) (st : σ) (r : Except κ Unit × σ),
    cfgFix T l st = some r → ∃ n k, count T n l st = some k := by
  refine cfgFix.fixpoint_induct T
    (fun f => ∀ l st r, f l st = some r → ∃ n k, count T n l st = some k) ?_ ?_
  · refine admissible_pi_apply
      (fun l (g : σ → UB (Except κ Unit × σ)) =>
        ∀ st r, g st = some r → ∃ n k, count T n l st = some k) fun l => ?_
    refine admissible_pi_apply
      (fun st (u : UB (Except κ Unit × σ)) =>
        ∀ r, u = some r → ∃ n k, count T n l st = some k) fun st => ?_
    exact admissible_flatOrder (b := (none : Option (Except κ Unit × σ)))
      (fun u => ∀ r, (show UB (Except κ Unit × σ) from u) = some r →
        ∃ n k, count T n l st = some k)
      (fun _ h => nomatch h)
  · intro f ih l st r h
    dsimp only at h
    cases hl : T.get? l with
    | none =>
      refine ⟨0 + 1, 0, ?_⟩
      rw [count, hl]
      rfl
    | some b =>
      rw [hl] at h
      obtain ⟨⟨r', st'⟩, hp, hr⟩ := Option.bind_eq_some_iff.mp h
      rcases r' with l' | _
      · obtain ⟨n, k, hk⟩ := ih l' st' r hr
        refine ⟨n + 1, k + 1, ?_⟩
        rw [count, hl]
        show (b.run.run st >>= _) = _
        rw [hp, some_bind]
        show (· + 1) <$> count T n l' st' = some (k + 1)
        rw [hk]
        rfl
      · refine ⟨0 + 1, 1, ?_⟩
        rw [count, hl]
        show (b.run.run st >>= _) = _
        rw [hp, some_bind]
        rfl

theorem count_unique : ∀ (n n' : Nat) (l : κ) (st : σ) (k k' : Nat),
    count T n l st = some k → count T n' l st = some k' → k = k'
  | 0, _, _, _, _, _, h, _ => nomatch h
  | _ + 1, 0, _, _, _, _, _, h' => nomatch h'
  | n + 1, n' + 1, l, st, k, k', h, h' => by
    rw [count] at h h'
    cases hl : T.get? l with
    | none =>
      rw [hl] at h h'
      have := Option.some.inj h
      have := Option.some.inj h'
      omega
    | some b =>
      rw [hl] at h h'
      obtain ⟨⟨r, st'⟩, hp, hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨r', st''⟩, hp', hr'⟩ := Option.bind_eq_some_iff.mp h'
      rw [hp] at hp'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
      rcases r with l' | _
      · obtain ⟨k₁, hk₁, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨k₂, hk₂, rfl⟩ := Option.map_eq_some_iff.mp hr'
        rw [count_unique n n' l' st' k₁ k₂ hk₁ hk₂]
      · have := Option.some.inj hr
        have := Option.some.inj hr'
        omega

open Classical in
noncomputable def steps (l : κ) (st : σ) : Nat :=
  if h : ∃ k n, count T n l st = some k then Classical.choose h else 0

theorem steps_eq {n : Nat} {l : κ} {st : σ} {k : Nat} (h : count T n l st = some k) :
    steps T l st = k := by
  have hex : ∃ k n, count T n l st = some k := ⟨k, n, h⟩
  simp only [steps, hex, ↓reduceDIte]
  obtain ⟨n', hn'⟩ := Classical.choose_spec hex
  exact count_unique T n' n l st _ k hn' h

theorem steps_lt {l l' : κ} {st st' : σ} {b : ExceptT κ (StateT σ UB) Unit} (hl : T.get? l = some b)
    (hrun : b.run.run st = some (.error l', st')) {r : Except κ Unit × σ}
    (hfix : cfgFix T l st = some r) : steps T l' st' < steps T l st := by
  obtain ⟨n, k, hk⟩ := count_of_cfgFix T l st r hfix
  cases n with
  | zero => exact nomatch hk
  | succ n =>
    have hk0 := hk
    rw [count, hl] at hk
    change (b.run.run st >>= _) = _ at hk
    rw [hrun, some_bind] at hk
    obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
    rw [steps_eq T hk0, steps_eq T hk']
    omega

end

end Ascent
