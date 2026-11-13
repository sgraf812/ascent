import Ascent.Table
import Ascent.FixLoop
import Ascent.Refinement.Lockstep

/-!
# Block loops

A block program runs in `ExceptT κ (StateT σ Demonic)`, and a jump to a label `l` is the exception `l`.
`cfgLoop stay T l` runs the blocks of the table `T` while the state satisfies `stay`: at a label `l`
with a block `b`, in a state `s` with `stay s`, it runs `b`; a jump of `b` continues the loop at its
target, and a normal end of `b` ends the loop. At a label without a block, or in a state without
`stay`, the loop leaves by throwing the label. For a machine, `stay` is the test that the stack
pointer still lies in the frame of the loop, so a return leaves the loop at any address.

`cfgLoop_header` makes a label `h` with block `b` the header of a loop over the remaining blocks:
running from `h` in a state with `stay` is a `repeat'` loop. An iteration runs `b` and then the loop
over `T.erase h`; leaving that loop at `h` in a state with `stay` continues the iteration, leaving it
otherwise leaves the `repeat'` loop. Applied at every label, the equation turns a table into nested
`repeat'` loops. It is Bekić's elimination of one variable from a system of fixpoint equations.

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

/-- The postcondition of a run of a block program, on the pair of its result and its state. -/
def runPost (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) : Except κ α × σ → Prop
  | (.ok a, s') => Q a s'
  | (.error e, s') => E.1 e s'

theorem wp_run_eq (x : ExceptT κ (StateT σ Demonic) α) (Q : α → σ → Prop)
    (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp x Q E s = (x.run.run s).wpD (runPost Q E) := by
  rw [ExceptT.wp_apply_eq, StateT.wp_apply_eq]
  show (x.run.run s).wpD _ = _
  congr 1
  funext p
  rcases p with ⟨_ | _, _⟩ <;> rfl

theorem wp_throw (l : κ) (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (throw l : ExceptT κ (StateT σ Demonic) α) Q E s = E.1 l s := by
  rw [wp_run_eq]
  rfl

theorem wp_tryCatch (x : ExceptT κ (StateT σ Demonic) α) (h : κ → ExceptT κ (StateT σ Demonic) α)
    (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (tryCatch x h) Q E s = wp x Q (fun l => wp (h l) Q E, E.2) s := by
  rw [wp_run_eq, wp_run_eq]
  show ((ExceptT.tryCatch x h).run.run s).wpD _ = _
  simp only [ExceptT.tryCatch, ExceptT.run_mk, StateT.run_bind, Demonic.wpD_bind]
  congr 1
  funext p
  rcases p with ⟨l | a, s'⟩
  · exact (wp_run_eq (h l) Q E s').symm
  · rfl

theorem ext_wp {x y : ExceptT κ (StateT σ Demonic) α}
    (h : ∀ (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) s, wp x Q E s → wp y Q E s)
    (h' : ∀ (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) s, wp y Q E s → wp x Q E s) :
    x = y := by
  have key : ∀ (u : ExceptT κ (StateT σ Demonic) α) s (P : Except κ α × σ → Prop),
      wp u (fun a st => P (.ok a, st)) (fun e st => P (.error e, st), estack⟨⟩) s = (u.run.run s).wpD P := by
    intro u s P
    rw [wp_run_eq]
    congr 1
    funext p
    rcases p with ⟨_ | _, _⟩ <;> rfl
  apply ExceptT.ext
  apply StateT.ext
  intro s
  refine Demonic.ext (funext fun P => propext ⟨fun hx => ?_, fun hy => ?_⟩)
  · rw [← key] at hx ⊢; exact h _ _ s hx
  · rw [← key] at hy ⊢; exact h' _ _ s hy

theorem tryCatch_throw (l : κ) (h : κ → ExceptT κ (StateT σ Demonic) α) :
    tryCatch (throw l : ExceptT κ (StateT σ Demonic) α) h = h l := by
  apply ext_wp <;> intro Q E s <;> rw [wp_tryCatch, wp_throw] <;> exact id

theorem throw_bind {β : Type} (l : κ) (k : α → ExceptT κ (StateT σ Demonic) β) :
    ((throw l : ExceptT κ (StateT σ Demonic) α) >>= k) = throw l := by
  apply ext_wp <;> intro Q E s <;> rw [WPMonadExact.wp_bind_eq, wp_throw, wp_throw] <;> exact id

theorem tryCatch_pure (a : α) (h : κ → ExceptT κ (StateT σ Demonic) α) : tryCatch (pure a) h = pure a := by
  apply ext_wp <;> intro Q E s <;> rw [wp_tryCatch] <;> simp only [WPMonadExact.wp_pure_eq] <;> exact id

theorem tryCatch_tryCatch (x : ExceptT κ (StateT σ Demonic) α) (h₁ h₂ : κ → ExceptT κ (StateT σ Demonic) α) :
    tryCatch (tryCatch x h₁) h₂ = tryCatch x (fun l => tryCatch (h₁ l) h₂) := by
  apply ext_wp <;> intro Q E s <;>
    simp only [wp_tryCatch, fun l => funext (wp_tryCatch (h₁ l) h₂ Q E)] <;> exact id

end

end BlockLoop

open BlockLoop

section
variable {κ σ α : Type}

def condState (c : σ → Bool) (x y : ExceptT κ (StateT σ Demonic) α) : ExceptT κ (StateT σ Demonic) α :=
  get >>= fun s => if c s then x else y

theorem condState_run (c : σ → Bool) (x y : ExceptT κ (StateT σ Demonic) α) (s : σ) :
    (condState c x y).run.run s = (if c s then x else y).run.run s := rfl

theorem wp_condState (c : σ → Bool) (x y : ExceptT κ (StateT σ Demonic) α) (Q : α → σ → Prop)
    (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (condState c x y) Q E s = if c s then wp x Q E s else wp y Q E s := by
  rw [wp_run_eq, condState_run]
  cases c s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [wp_run_eq]

theorem condState_const (b : Bool) (x y : ExceptT κ (StateT σ Demonic) α) :
    condState (fun _ => b) x y = if b = true then x else y := by
  cases b <;> apply ext_wp <;> intro Q E s <;> simp [wp_condState]

theorem condState_true (x y : ExceptT κ (StateT σ Demonic) α) : condState (fun _ => true) x y = x := by
  simpa using condState_const true x y

theorem condState_false (x y : ExceptT κ (StateT σ Demonic) α) : condState (fun _ => false) x y = y := by
  simpa using condState_const false x y

theorem condState_self (c : σ → Bool) (x : ExceptT κ (StateT σ Demonic) α) : condState c x x = x := by
  apply ext_wp <;> intro Q E s <;> rw [wp_condState] <;> split <;> exact id

theorem tryCatch_condState (c : σ → Bool) (x y : ExceptT κ (StateT σ Demonic) α)
    (h : κ → ExceptT κ (StateT σ Demonic) α) :
    tryCatch (condState c x y) h = condState c (tryCatch x h) (tryCatch y h) := by
  apply ext_wp <;> intro Q E s <;> simp only [wp_tryCatch, wp_condState] <;> split <;> exact id

theorem condState_bind {β : Type} (c : σ → Bool) (x y : ExceptT κ (StateT σ Demonic) α)
    (k : α → ExceptT κ (StateT σ Demonic) β) :
    (condState c x y >>= k) = condState c (x >>= k) (y >>= k) := by
  apply ext_wp <;> intro Q E s <;> simp only [WPMonadExact.wp_bind_eq, wp_condState] <;> split <;>
    exact id


end

section
variable {κ σ : Type} [DecidableEq κ]

def cfgFix (stay : σ → Bool) (T : Table κ (ExceptT κ (StateT σ Demonic) Unit)) (l : κ) (s : σ) :
    Demonic (Except κ Unit × σ) :=
  if stay s then
    match T.get? l with
    | none => pure (.error l, s)
    | some b => b.run.run s >>= fun p =>
      match p.1 with
      | .ok _ => pure (.ok (), p.2)
      | .error l' => cfgFix stay T l' p.2
  else pure (.error l, s)
partial_fixpoint

def cfgLoop (stay : σ → Bool) (T : Table κ (ExceptT κ (StateT σ Demonic) Unit)) (l : κ) :
    ExceptT κ (StateT σ Demonic) Unit :=
  cfgFix stay T l

variable (stay : σ → Bool) (T : Table κ (ExceptT κ (StateT σ Demonic) Unit))

def cfgStep (f : κ → ExceptT κ (StateT σ Demonic) Unit) (l : κ) : ExceptT κ (StateT σ Demonic) Unit :=
  show σ → Demonic (Except κ Unit × σ) from fun s =>
    if stay s then
      match T.get? l with
      | none => pure (.error l, s)
      | some b => b.run.run s >>= fun p =>
        match p.1 with
        | .ok _ => pure (.ok (), p.2)
        | .error l' => (f l').run.run p.2
    else pure (.error l, s)

theorem cfgLoop_eq_cfgStep : cfgLoop stay T = cfgStep stay T (cfgLoop stay T) := by
  funext l
  show (cfgFix stay T l : σ → Demonic (Except κ Unit × σ)) = cfgStep stay T _ l
  funext s
  rw [cfgFix]
  rfl

theorem cfgLoop_induct (motive : (κ → ExceptT κ (StateT σ Demonic) Unit) → Prop) (hadm : admissible motive)
    (h : ∀ f, motive f → motive (cfgStep stay T f)) : motive (cfgLoop stay T) :=
  cfgFix.fixpoint_induct stay T motive hadm h

theorem cfgLoop_run (l : κ) (s : σ) : (cfgLoop stay T l).run.run s = cfgFix stay T l s := rfl

section
variable (f : κ → ExceptT κ (StateT σ Demonic) Unit) {l : κ} (Q : Unit → σ → Prop)
  (E : (κ → σ → Prop) × EStack⟨⟩) {s : σ}

theorem cfgStep_run_none (hl : T.get? l = none) :
    (cfgStep stay T f l).run.run s = pure (.error l, s) := by
  simp only [cfgStep, ExceptT.run, StateT.run, hl]
  split <;> rfl

theorem cfgStep_run_leave (hs : stay s = false) :
    (cfgStep stay T f l).run.run s = pure (.error l, s) := by
  simp only [cfgStep, ExceptT.run, StateT.run, hs, Bool.false_eq_true, ↓reduceIte]

theorem cfgStep_run_some {b : ExceptT κ (StateT σ Demonic) Unit} (hl : T.get? l = some b)
    (hs : stay s = true) :
    (cfgStep stay T f l).run.run s = (b.run.run s >>= fun p =>
      match p.1 with
      | .ok _ => pure (.ok (), p.2)
      | .error l' => (f l').run.run p.2) := by
  simp only [cfgStep, ExceptT.run, StateT.run, hl, hs, ↓reduceIte]

theorem wp_cfgStep_none (hl : T.get? l = none) : wp (cfgStep stay T f l) Q E s = E.1 l s := by
  rw [wp_run_eq, cfgStep_run_none _ _ _ hl]
  rfl

theorem wp_cfgStep_leave (hs : stay s = false) : wp (cfgStep stay T f l) Q E s = E.1 l s := by
  rw [wp_run_eq, cfgStep_run_leave _ _ _ hs]
  rfl

theorem wp_cfgStep_some {b : ExceptT κ (StateT σ Demonic) Unit} (hl : T.get? l = some b)
    (hs : stay s = true) :
    wp (cfgStep stay T f l) Q E s = wp b Q (fun l' => wp (f l') Q E, E.2) s := by
  rw [wp_run_eq, wp_run_eq b, cfgStep_run_some _ _ _ hl hs, Demonic.wpD_bind]
  congr 1
  funext p
  rcases p with ⟨l' | ⟨⟩, s'⟩
  · exact (wp_run_eq (f l') Q E s').symm
  · rfl

end

section
variable {l : κ} (Q : Unit → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) {s : σ}

theorem wp_cfgLoop_none (hl : T.get? l = none) : wp (cfgLoop stay T l) Q E s = E.1 l s := by
  rw [congrFun (cfgLoop_eq_cfgStep stay T) l, wp_cfgStep_none _ _ _ _ _ hl]

theorem wp_cfgLoop_leave (hs : stay s = false) : wp (cfgLoop stay T l) Q E s = E.1 l s := by
  rw [congrFun (cfgLoop_eq_cfgStep stay T) l, wp_cfgStep_leave _ _ _ _ _ hs]

theorem wp_cfgLoop_some {b : ExceptT κ (StateT σ Demonic) Unit} (hl : T.get? l = some b)
    (hs : stay s = true) :
    wp (cfgLoop stay T l) Q E s = wp b Q (fun l' => wp (cfgLoop stay T l') Q E, E.2) s := by
  rw [congrFun (cfgLoop_eq_cfgStep stay T) l, wp_cfgStep_some _ _ _ _ _ hl hs]

end

theorem cfgLoop_none {l : κ} (hl : T.get? l = none) : cfgLoop stay T l = throw l := by
  apply ext_wp <;> intro Q E s <;> rw [wp_cfgLoop_none _ _ _ _ hl, wp_throw] <;> exact id

theorem cfgLoop_some {l : κ} {b : ExceptT κ (StateT σ Demonic) Unit} (hl : T.get? l = some b) :
    cfgLoop stay T l = condState stay (tryCatch b (cfgLoop stay T)) (throw l) := by
  apply ext_wp <;> intro Q E s <;> rw [wp_condState] <;> cases hs : stay s
  all_goals first
    | simp only [wp_cfgLoop_leave _ _ _ _ hs, wp_throw, Bool.false_eq_true, ↓reduceIte]; exact id
    | simp only [wp_cfgLoop_some _ _ _ _ hl hs, wp_tryCatch, ↓reduceIte]; exact id

omit [DecidableEq κ] in
theorem admissible_wp_imp_fn (P : κ → (Unit → σ → Prop) → ((κ → σ → Prop) × EStack⟨⟩) → σ → Prop) :
    admissible fun f : κ → ExceptT κ (StateT σ Demonic) Unit =>
      ∀ l Q E s, wp (f l) Q E s → P l Q E s :=
  admissible_pi _ fun l => admissible_pi _ fun Q => admissible_pi _ fun E => admissible_pi _ fun s =>
    admissible_apply (fun _ u => wp u Q E s → P l Q E s) l (admissible_wp_imp _ E s _)

/-! ## Label elimination -/

theorem wp_header_body (h : κ) (b : ExceptT κ (StateT σ Demonic) Unit) (R : ForInStep PUnit → σ → Prop)
    (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (tryCatch (tryCatch b (cfgLoop stay (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
        (fun l' => if l' = h then condState stay (pure (ForInStep.yield PUnit.unit)) (throw l')
          else throw l')) R E s
      = wp b (fun _ => R (.done PUnit.unit))
          (fun l' => wp (cfgLoop stay (T.erase h) l') (fun _ => R (.done PUnit.unit))
            (fun l'' t => if l'' = h then (if stay t then R (.yield PUnit.unit) t else E.1 l'' t)
              else E.1 l'' t, E.2), E.2) s := by
  have hH : (fun l' => wp ((if l' = h then condState stay (pure (ForInStep.yield PUnit.unit)) (throw l')
      else throw l' : ExceptT κ (StateT σ Demonic) (ForInStep PUnit))) R E)
      = fun l' t => if l' = h then (if stay t then R (.yield PUnit.unit) t else E.1 l' t) else E.1 l' t := by
    funext l' t
    split
    · rw [wp_condState]
      simp only [WPMonadExact.wp_pure_eq, wp_throw]
    · exact wp_throw _ _ _ _
  rw [wp_tryCatch, hH, WPMonadExact.wp_bind_eq]
  simp only [WPMonadExact.wp_pure_eq]
  rw [wp_tryCatch]

theorem unit_post (Q : Unit → σ → Prop) : (fun _ : Unit => Q ()) = Q := funext fun u => by cases u; rfl

section
variable {h : κ} {b : ExceptT κ (StateT σ Demonic) Unit} (hb : T.get? h = some b)
include hb

theorem wp_cfgLoop_imp_forIn (Q : Unit → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (cfgLoop stay T h) Q E s → wp (condState stay (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop stay (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then condState stay (pure (ForInStep.yield PUnit.unit)) (throw l')
        else throw l'))) (throw h)) Q E s := by
  let loop := FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop stay (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then condState stay (pure (ForInStep.yield PUnit.unit)) (throw l')
        else throw l'))
  let G : ExceptT κ (StateT σ Demonic) Unit := condState stay loop (throw h)
  let H : κ → ExceptT κ (StateT σ Demonic) Unit := fun l' => if l' = h then G else throw l'
  have hG : ∀ (Q : Unit → σ → Prop) E t, wp G Q E t = if stay t then wp loop Q E t else E.1 h t := by
    intro Q E t
    simp only [G, wp_condState, wp_throw]
  have hH : ∀ (Q : Unit → σ → Prop) E, (fun l'' => wp (H l'') Q E)
      = fun l'' => if l'' = h then wp G Q E else E.1 l'' := by
    intro Q E
    funext l'' t
    simp only [H]
    split
    · rfl
    · exact wp_throw _ _ _ _
  have hnone : (T.erase h).get? h = none := by simp only [Table.get?_erase, ↓reduceIte]
  have hloop : ∀ (Q : Unit → σ → Prop) E s,
      wp loop Q E s = wp b (fun _ => Q ()) (fun l' => wp (cfgLoop stay (T.erase h) l') (fun _ => Q ())
        (fun l'' => if l'' = h then wp G Q E else E.1 l'', E.2), E.2) s := by
    intro Q E s
    refine (congrFun (FixLoop.wp_forIn_eq _ _ _ Q E) s).trans ?_
    rw [wp_header_body]
    refine congrArg (fun F => wp b (fun _ => Q ()) (F, E.2) s) (funext fun l' => ?_)
    refine congrArg (fun F => wp (cfgLoop stay (T.erase h) l') (fun _ => Q ()) (F, E.2))
      (funext fun l'' => funext fun t => ?_)
    split
    · next he => subst he; rw [hG]
    · rfl
  have key := cfgLoop_induct stay T
    (fun f => ∀ l Q E s, wp (f l) Q E s → wp (tryCatch (cfgLoop stay (T.erase h) l) H) Q E s)
    (admissible_wp_imp_fn _)
  refine fun hw => ?_
  have hR := (key ?_) h Q E s hw
  · rw [wp_tryCatch, wp_cfgLoop_none _ _ _ _ hnone, hH] at hR
    simpa only [↓reduceIte] using hR
  intro f ih l Q E s hwf
  rw [wp_tryCatch, hH]
  cases hs : stay s with
  | false =>
    rw [wp_cfgStep_leave _ _ _ _ _ hs] at hwf
    rw [wp_cfgLoop_leave _ _ _ _ hs]
    by_cases hlh : l = h
    · subst hlh
      simp only [↓reduceIte, hG, hs, Bool.false_eq_true]
      exact hwf
    · simpa only [hlh, ↓reduceIte] using hwf
  | true =>
  cases hl : T.get? l with
  | none =>
    have hne : l ≠ h := fun he => by rw [he, hb] at hl; exact nomatch hl
    rw [wp_cfgStep_none _ _ _ _ _ hl] at hwf
    have hl' : (T.erase h).get? l = none := by simp only [Table.get?_erase, hne, hl, ↓reduceIte]
    rw [wp_cfgLoop_none _ _ _ _ hl']
    simpa only [hne, ↓reduceIte] using hwf
  | some b' =>
    rw [wp_cfgStep_some _ _ _ _ _ hl hs] at hwf
    by_cases hlh : l = h
    · subst hlh
      rw [hb] at hl
      obtain rfl := Option.some.inj hl
      rw [wp_cfgLoop_none _ _ _ _ hnone]
      simp only [↓reduceIte, hG, hs]
      rw [hloop, unit_post]
      refine WP.wp_monotone (x := b) (fun _ _ ht => ht) ?_ s hwf
      refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l' t ht
      have := ih l' Q E t ht
      rw [wp_tryCatch, hH] at this
      exact this
    · have hl' : (T.erase h).get? l = some b' := by simp only [Table.get?_erase, hlh, hl, ↓reduceIte]
      rw [wp_cfgLoop_some _ _ _ _ hl' hs]
      refine WP.wp_monotone (x := b') (fun _ _ ht => ht) ?_ s hwf
      refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l' t ht
      have := ih l' Q E t ht
      rw [wp_tryCatch, hH] at this
      exact this

theorem wp_forIn_imp_cfgLoop (Q : Unit → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (condState stay (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop stay (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then condState stay (pure (ForInStep.yield PUnit.unit)) (throw l')
        else throw l'))) (throw h)) Q E s →
      wp (cfgLoop stay T h) Q E s := by
  have inner : ∀ (g : PUnit → ExceptT κ (StateT σ Demonic) PUnit),
      (∀ (Q : Unit → σ → Prop) E s, stay s = true → wp (g PUnit.unit) Q E s →
        wp (cfgLoop stay T h) Q E s) →
      ∀ (Q : Unit → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) l s,
        wp (cfgLoop stay (T.erase h) l) Q
          (fun l'' t => if l'' = h then (if stay t then wp (g PUnit.unit) Q E t else E.1 l'' t)
            else E.1 l'' t, E.2) s →
        wp (cfgLoop stay T l) Q E s := by
    intro g hg Q E
    let E' : (κ → σ → Prop) × EStack⟨⟩ :=
      (fun l'' t => if l'' = h then (if stay t then wp (g PUnit.unit) Q E t else E.1 l'' t)
        else E.1 l'' t, E.2)
    have hE'h : ∀ t, E'.1 h t → wp (cfgLoop stay T h) Q E t := by
      intro t ht
      cases hs : stay t
      · simp only [E', hs, ↓reduceIte, Bool.false_eq_true] at ht
        rw [wp_cfgLoop_leave _ _ _ _ hs]
        exact ht
      · simp only [E', hs, ↓reduceIte] at ht
        exact hg Q E t hs ht
    have := cfgLoop_induct stay (T.erase h)
      (fun f => ∀ l s, wp (f l) Q E' s → wp (cfgLoop stay T l) Q E s)
      (admissible_pi _ fun l => admissible_pi _ fun s =>
        admissible_apply (fun _ u => wp u Q E' s → _) l (admissible_wp_imp _ E' s _))
    refine this ?_
    intro f ih l s hw
    cases hs : stay s with
    | false =>
      rw [wp_cfgStep_leave _ _ _ _ _ hs] at hw
      by_cases hlh : l = h
      · subst hlh
        exact hE'h s hw
      · simp only [E', hlh, ↓reduceIte] at hw
        rw [wp_cfgLoop_leave _ _ _ _ hs]
        exact hw
    | true =>
    cases hl : (T.erase h).get? l with
    | none =>
      rw [wp_cfgStep_none _ _ _ _ _ hl] at hw
      by_cases hlh : l = h
      · subst hlh
        exact hE'h s hw
      · simp only [E', hlh, ↓reduceIte] at hw
        have hT : T.get? l = none := by simpa only [Table.get?_erase, hlh, ↓reduceIte] using hl
        rw [wp_cfgLoop_none _ _ _ _ hT]
        exact hw
    | some b' =>
      have hlh : l ≠ h := fun he => by simp only [he, Table.get?_erase, ↓reduceIte] at hl; exact nomatch hl
      have hT : T.get? l = some b' := by simpa only [Table.get?_erase, hlh, ↓reduceIte] using hl
      rw [wp_cfgStep_some _ _ _ _ _ hl hs] at hw
      rw [wp_cfgLoop_some _ _ _ _ hT hs]
      refine WP.wp_monotone (x := b') (fun _ _ ht => ht) ?_ s hw
      refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l' t ht
      exact ih l' t ht
  have := FixLoop.forIn_induct (m := ExceptT κ (StateT σ Demonic)) (β := PUnit) (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop stay (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
      (fun l' => if l' = h then condState stay (pure (ForInStep.yield PUnit.unit)) (throw l')
        else throw l'))
    (fun g => ∀ (Q : Unit → σ → Prop) E s, stay s = true → wp (g PUnit.unit) Q E s →
      wp (cfgLoop stay T h) Q E s)
    (admissible_pi _ fun Q => admissible_pi _ fun E => admissible_pi _ fun s => admissible_pi _ fun _ =>
      admissible_apply (fun _ u => wp u Q E s → _) PUnit.unit (admissible_wp_imp _ E s _))
  intro hw0
  rw [wp_condState] at hw0
  cases hs0 : stay s with
  | false =>
    simp only [hs0, Bool.false_eq_true, ↓reduceIte, wp_throw] at hw0
    rw [wp_cfgLoop_leave _ _ _ _ hs0]
    exact hw0
  | true =>
  simp only [hs0, ↓reduceIte] at hw0
  refine this ?_ Q E s hs0 hw0
  intro g ih Q E s hs hw
  rw [FixLoop.step, WPMonadExact.wp_bind_eq, wp_header_body] at hw
  simp only [WPMonadExact.wp_pure_eq] at hw
  rw [wp_cfgLoop_some _ _ _ _ hb hs]
  rw [← unit_post Q]
  refine WP.wp_monotone (x := b) (fun _ _ ht => ht) ?_ s hw
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro l' t ht
  rw [unit_post]
  rw [unit_post] at ht
  exact inner g ih Q E l' t ht

theorem cfgLoop_header_of_some : cfgLoop stay T h = condState stay (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch b (cfgLoop stay (T.erase h)) >>= fun _ => pure (ForInStep.done PUnit.unit))
        (fun l' => if l' = h then condState stay (pure (ForInStep.yield PUnit.unit)) (throw l')
          else throw l'))) (throw h) :=
  ext_wp (wp_cfgLoop_imp_forIn stay T hb) (wp_forIn_imp_cfgLoop stay T hb)

end

theorem cfgLoop_header {h : κ} (hb : (T.get? h).isSome = true) :
    cfgLoop stay T h = condState stay (FixLoop.mk.forIn PUnit.unit (fun _ _ =>
      tryCatch (tryCatch ((T.get? h).getD (throw h)) (cfgLoop stay (T.erase h)) >>= fun _ =>
          pure (ForInStep.done PUnit.unit))
        (fun l' => if l' = h then condState stay (pure (ForInStep.yield PUnit.unit)) (throw l')
          else throw l'))) (throw h) := by
  obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp hb
  rw [hb']
  exact cfgLoop_header_of_some stay T hb'

theorem cfgLoop_eq_throw {l : κ} (hl : T.get? l = none) : cfgLoop stay T l = throw l :=
  cfgLoop_none stay T hl

/-! ## The exception effect of a program -/

/-- `x` throws a label `l` in a state `t` only if `P l t`. -/
def ThrowsOnly {α : Type} (P : κ → σ → Prop) (x : ExceptT κ (StateT σ Demonic) α) : Prop :=
  ∀ (Q : α → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) s,
    wp x Q E s → wp x Q (fun l t => P l t ∧ E.1 l t, E.2) s

section
variable {α β : Type} {P : κ → σ → Prop}

omit [DecidableEq κ] in
theorem ThrowsOnly.pure (a : α) : ThrowsOnly P (pure a : ExceptT κ (StateT σ Demonic) α) = True := eq_true <| by
  intro Q E s hw
  simpa only [WPMonadExact.wp_pure_eq] using hw

omit [DecidableEq κ] in
theorem ThrowsOnly.throw {l : κ} (hl : ∀ s, P l s) :
    ThrowsOnly P (throw l : ExceptT κ (StateT σ Demonic) α) = True := eq_true <| by
  intro Q E s hw
  rw [wp_throw] at hw ⊢
  exact ⟨hl s, hw⟩

omit [DecidableEq κ] in
theorem ThrowsOnly.bind {x : ExceptT κ (StateT σ Demonic) α} {k : α → ExceptT κ (StateT σ Demonic) β}
    (hx : ThrowsOnly P x) (hk : ∀ a, ThrowsOnly P (k a)) : ThrowsOnly P (x >>= k) = True := eq_true <| by
  intro Q E s hw
  rw [WPMonadExact.wp_bind_eq] at hw ⊢
  exact WP.wp_monotone (x := x) (fun a t ht => hk a Q E t ht) PartialOrder.rel_refl s
    (hx _ _ s hw)

omit [DecidableEq κ] in
theorem ThrowsOnly.map {x : ExceptT κ (StateT σ Demonic) α} (f : α → β) (hx : ThrowsOnly P x) :
    ThrowsOnly P (f <$> x) = True := eq_true <| by
  rw [map_eq_pure_bind]
  exact of_eq_true (ThrowsOnly.bind hx fun _ => of_eq_true (ThrowsOnly.pure _))

theorem ThrowsOnly.tryCatch {x : ExceptT κ (StateT σ Demonic) α} {h : κ} {y : ExceptT κ (StateT σ Demonic) α}
    (hx : ThrowsOnly (fun l s => l = h ∨ P l s) x) (hy : ThrowsOnly P y) :
    ThrowsOnly P (tryCatch x (fun l' => if l' = h then y else MonadExcept.throw l')) = True := eq_true <| by
  intro Q E s hw
  rw [wp_tryCatch] at hw ⊢
  refine WP.wp_monotone (x := x) (fun _ _ ht => ht) ?_ s (hx _ _ s hw)
  refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
  intro l t ⟨hl, ht⟩
  by_cases hlh : l = h
  · simp only [hlh, ↓reduceIte] at ht ⊢
    exact hy Q E t ht
  · simp only [hlh, ↓reduceIte, wp_throw] at ht ⊢
    exact ⟨hl.resolve_left hlh, ht⟩

omit [DecidableEq κ] in
theorem ThrowsOnly.forIn {b : α} {f : Unit → α → ExceptT κ (StateT σ Demonic) (ForInStep α)}
    (hf : ∀ u v, ThrowsOnly P (f u v)) : ThrowsOnly P (FixLoop.mk.forIn b f) = True := eq_true <| by
  haveI : Nonempty α := ⟨b⟩
  have := FixLoop.forIn_induct (m := ExceptT κ (StateT σ Demonic)) f
    (fun g => ∀ v (Q : α → σ → Prop) E s, wp (g v) Q E s →
      wp (FixLoop.mk.forIn v f) Q (fun l t => P l t ∧ E.1 l t, E.2) s)
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

omit [DecidableEq κ] in
theorem ThrowsOnly.condState (c : σ → Bool) {x y : ExceptT κ (StateT σ Demonic) α} (hx : ThrowsOnly P x)
    (hy : ThrowsOnly P y) : ThrowsOnly P (condState c x y) = True := eq_true <| by
  intro Q E s hw
  rw [wp_condState] at hw ⊢
  by_cases hc : c s = true
  · rw [ite_eq_left hc] at hw ⊢
    exact hx _ _ s hw
  · rw [ite_eq_right hc] at hw ⊢
    exact hy _ _ s hw

end

omit [DecidableEq κ] in
/-- A handler `H` that throws on every label a loop may throw crosses the loop. -/
theorem tryCatch_forIn_bind_of {β γ : Type} {P : κ → σ → Prop} {i : β}
    {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)} {k : β → ExceptT κ (StateT σ Demonic) γ}
    {H : κ → ExceptT κ (StateT σ Demonic) γ}
    (hH : ∀ (Q : γ → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) l t, P l t → (wp (H l) Q E t ↔ E.1 l t))
    (hf : ThrowsOnly P (FixLoop.mk.forIn i f)) :
    tryCatch (FixLoop.mk.forIn i f >>= k) H = FixLoop.mk.forIn i f >>= fun r => tryCatch (k r) H := by
  apply ext_wp
  · intro Q E s hw
    rw [wp_tryCatch, WPMonadExact.wp_bind_eq] at hw
    rw [WPMonadExact.wp_bind_eq]
    refine WP.wp_monotone (x := FixLoop.mk.forIn i f) (fun r t ht => ?_) ?_ s (hf _ _ s hw)
    · rw [wp_tryCatch]; exact ht
    · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l t ⟨hl, ht⟩
      exact (hH Q E l t hl).mp ht
  · intro Q E s hw
    rw [WPMonadExact.wp_bind_eq] at hw
    rw [wp_tryCatch, WPMonadExact.wp_bind_eq]
    refine WP.wp_monotone (x := FixLoop.mk.forIn i f) (fun r t ht => ?_) ?_ s (hf _ _ s hw)
    · rw [wp_tryCatch] at ht; exact ht
    · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l t ⟨hl, ht⟩
      exact (hH Q E l t hl).mpr ht

omit [DecidableEq κ] in
theorem tryCatch_map_forIn_of {β γ : Type} {P : κ → σ → Prop} {i : β}
    {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)} {g : β → γ} {H : κ → ExceptT κ (StateT σ Demonic) γ}
    (hH : ∀ (Q : γ → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) l t, P l t → (wp (H l) Q E t ↔ E.1 l t))
    (hf : ThrowsOnly P (FixLoop.mk.forIn i f)) :
    tryCatch (g <$> FixLoop.mk.forIn i f) H = g <$> FixLoop.mk.forIn i f := by
  have hp : ∀ r : β, tryCatch (pure (g r) : ExceptT κ (StateT σ Demonic) γ) H = pure (g r) := fun r => by
    apply ext_wp <;> intro Q E s <;> rw [wp_tryCatch] <;>
      simp only [WPMonadExact.wp_pure_eq] <;> exact id
  have := tryCatch_forIn_bind_of (k := fun r => pure (g r)) hH hf
  simp only [hp] at this
  simpa only [map_eq_pure_bind] using this

omit [DecidableEq κ] in
theorem handler_throws {γ : Type} {h l : κ} [Decidable (l = h)] {y : ExceptT κ (StateT σ Demonic) γ}
    (Q : γ → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (t : σ) (hl : l ≠ h) :
    wp (if l = h then y else throw l) Q E t ↔ E.1 l t := by
  simp only [hl, ↓reduceIte, wp_throw]

omit [DecidableEq κ] in
theorem header_handler_throws {γ : Type} {h l : κ} [Decidable (l = h)] {c : σ → Bool}
    {y : ExceptT κ (StateT σ Demonic) γ} (Q : γ → σ → Prop) (E : (κ → σ → Prop) × EStack⟨⟩) (t : σ)
    (hl : l ≠ h ∨ c t = false) :
    wp (if l = h then condState c y (throw l) else throw l) Q E t ↔ E.1 l t := by
  by_cases hlh : l = h
  · simp only [hlh, ↓reduceIte, wp_condState, wp_throw]
    simp only [hlh, ne_eq, not_true_eq_false, false_or] at hl
    simp [hl]
  · simp only [hlh, ↓reduceIte, wp_throw]

/-- A handler that catches only `h` crosses a loop that never throws `h`. -/
theorem tryCatch_forIn_bind {β γ : Type} {h : κ} {i : β} {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)}
    {k : β → ExceptT κ (StateT σ Demonic) γ} {y : ExceptT κ (StateT σ Demonic) γ}
    (hf : ThrowsOnly (fun l _ => l ≠ h) (FixLoop.mk.forIn i f)) :
    tryCatch (FixLoop.mk.forIn i f >>= k) (fun l' => if l' = h then y else throw l')
      = FixLoop.mk.forIn i f >>= fun r => tryCatch (k r) (fun l' => if l' = h then y else throw l') :=
  tryCatch_forIn_bind_of (fun Q E _ t hl => handler_throws Q E t hl) hf

theorem tryCatch_map_forIn {β γ : Type} {h : κ} {i : β}
    {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)} {g : β → γ} {y : ExceptT κ (StateT σ Demonic) γ}
    (hf : ThrowsOnly (fun l _ => l ≠ h) (FixLoop.mk.forIn i f)) :
    tryCatch (g <$> FixLoop.mk.forIn i f) (fun l' => if l' = h then y else throw l')
      = g <$> FixLoop.mk.forIn i f :=
  tryCatch_map_forIn_of (fun Q E _ t hl => handler_throws Q E t hl) hf

theorem tryCatch_forIn {β : Type} {h : κ} {i : β} {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)}
    {y : ExceptT κ (StateT σ Demonic) β} (hf : ThrowsOnly (fun l _ => l ≠ h) (FixLoop.mk.forIn i f)) :
    tryCatch (FixLoop.mk.forIn i f) (fun l' => if l' = h then y else throw l') = FixLoop.mk.forIn i f := by
  simpa only [id_map] using tryCatch_map_forIn (g := id) (y := y) hf

/-- A header handler crosses a loop that throws its header only in states without the stay test. -/
theorem tryCatch_forIn_bind_header {β γ : Type} {h : κ} {c : σ → Bool} {i : β}
    {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)}
    {k : β → ExceptT κ (StateT σ Demonic) γ} {y : ExceptT κ (StateT σ Demonic) γ}
    (hf : ThrowsOnly (fun l t => l ≠ h ∨ c t = false) (FixLoop.mk.forIn i f)) :
    tryCatch (FixLoop.mk.forIn i f >>= k) (fun l' => if l' = h then condState c y (throw l') else throw l')
      = FixLoop.mk.forIn i f >>= fun r =>
          tryCatch (k r) (fun l' => if l' = h then condState c y (throw l') else throw l') :=
  tryCatch_forIn_bind_of (fun Q E _ t hl => header_handler_throws Q E t hl) hf

theorem tryCatch_map_forIn_header {β γ : Type} {h : κ} {c : σ → Bool} {i : β}
    {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)} {g : β → γ} {y : ExceptT κ (StateT σ Demonic) γ}
    (hf : ThrowsOnly (fun l t => l ≠ h ∨ c t = false) (FixLoop.mk.forIn i f)) :
    tryCatch (g <$> FixLoop.mk.forIn i f) (fun l' => if l' = h then condState c y (throw l') else throw l')
      = g <$> FixLoop.mk.forIn i f :=
  tryCatch_map_forIn_of (fun Q E _ t hl => header_handler_throws Q E t hl) hf

theorem tryCatch_forIn_header {β : Type} {h : κ} {c : σ → Bool} {i : β}
    {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)} {y : ExceptT κ (StateT σ Demonic) β}
    (hf : ThrowsOnly (fun l t => l ≠ h ∨ c t = false) (FixLoop.mk.forIn i f)) :
    tryCatch (FixLoop.mk.forIn i f) (fun l' => if l' = h then condState c y (throw l') else throw l')
      = FixLoop.mk.forIn i f := by
  simpa only [id_map] using tryCatch_map_forIn_header (g := id) (y := y) hf

theorem tryCatch_forIn_return {β : Type} {e : κ} {i r : β}
    {f : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β)} :
    tryCatch (FixLoop.mk.forIn i f) (fun l => if l = e then pure r else throw l)
      = FixLoop.mk.forIn i (fun u v =>
          tryCatch (f u v) (fun l => if l = e then pure (ForInStep.done r) else throw l)) := by
  haveI : Nonempty β := ⟨i⟩
  let f' : Unit → β → ExceptT κ (StateT σ Demonic) (ForInStep β) := fun u v =>
    tryCatch (f u v) (fun l => if l = e then pure (ForInStep.done r) else throw l)
  apply ext_wp
  · intro Q E s hw
    rw [wp_tryCatch] at hw
    have := FixLoop.forIn_induct (m := ExceptT κ (StateT σ Demonic)) f
      (fun g => ∀ v t, wp (g v) Q (fun l => wp (if l = e then pure r else throw l : ExceptT κ (StateT σ Demonic) β) Q E, E.2) t →
        wp (FixLoop.mk.forIn v f') Q E t)
      (admissible_pi _ fun v => admissible_pi _ fun t =>
        admissible_apply (fun _ u => wp u Q _ t → _) v (admissible_wp_imp _ _ t _))
    refine this ?_ i s hw
    intro g ih v t hv
    rw [FixLoop.step, WPMonadExact.wp_bind_eq] at hv
    rw [FixLoop.wp_forIn_eq, wp_tryCatch]
    refine WP.wp_monotone (x := f () v) (fun x t' hx => ?_) ?_ t hv
    · cases x with
      | done v' => simpa only [WPMonadExact.wp_pure_eq] using hx
      | yield v' => exact ih v' t' hx
    · refine Prod.mk_le _ _ _ (fun l t' hl => ?_) PartialOrder.rel_refl
      by_cases he : l = e
      · simp only [he, ↓reduceIte, WPMonadExact.wp_pure_eq] at hl ⊢
        exact hl
      · simp only [he, ↓reduceIte, wp_throw] at hl ⊢
        exact hl
  · intro Q E s hw
    rw [wp_tryCatch]
    have := FixLoop.forIn_induct (m := ExceptT κ (StateT σ Demonic)) f'
      (fun g => ∀ v t, wp (g v) Q E t →
        wp (FixLoop.mk.forIn v f) Q (fun l => wp (if l = e then pure r else throw l : ExceptT κ (StateT σ Demonic) β) Q E, E.2) t)
      (admissible_pi _ fun v => admissible_pi _ fun t =>
        admissible_apply (fun _ u => wp u Q _ t → _) v (admissible_wp_imp _ _ t _))
    refine this ?_ i s hw
    intro g ih v t hv
    rw [FixLoop.step, WPMonadExact.wp_bind_eq, wp_tryCatch] at hv
    rw [FixLoop.wp_forIn_eq]
    refine WP.wp_monotone (x := f () v) (fun x t' hx => ?_) ?_ t hv
    · cases x with
      | done v' => simpa only [WPMonadExact.wp_pure_eq] using hx
      | yield v' => exact ih v' t' hx
    · refine Prod.mk_le _ _ _ (fun l t' hl => ?_) PartialOrder.rel_refl
      by_cases he : l = e
      · simp only [he, ↓reduceIte, WPMonadExact.wp_pure_eq] at hl ⊢
        exact hl
      · simp only [he, ↓reduceIte, wp_throw] at hl ⊢
        exact hl

omit [DecidableEq κ] in
theorem forIn_bind_done {β : Type} (b : PUnit) (x : ExceptT κ (StateT σ Demonic) β) :
    FixLoop.mk.forIn b (fun _ _ => x >>= fun _ => pure (ForInStep.done PUnit.unit)) = x >>= fun _ => pure PUnit.unit := by
  rw [FixLoop.forIn_eq, bind_assoc]
  simp only [pure_bind]

omit [DecidableEq κ] in
theorem condState_condState_left (c : σ → Bool) {α : Type} (x y z : ExceptT κ (StateT σ Demonic) α) :
    condState c (condState c x y) z = condState c x z := by
  apply ext_wp <;> intro Q E s <;> simp only [wp_condState] <;> cases c s <;> exact id

omit [DecidableEq κ] in
theorem condState_condState_right (c : σ → Bool) {α : Type} (x y z : ExceptT κ (StateT σ Demonic) α) :
    condState c x (condState c y z) = condState c x z := by
  apply ext_wp <;> intro Q E s <;> simp only [wp_condState] <;> cases c s <;> exact id

omit [DecidableEq κ] in
theorem condState_map {α β : Type} (c : σ → Bool) (f : α → β) (x y : ExceptT κ (StateT σ Demonic) α) :
    condState c (f <$> x) (f <$> y) = f <$> condState c x y := by
  simp only [map_eq_pure_bind, condState_bind]

omit [DecidableEq κ] in
theorem bind_map {α β γ : Type} (x : ExceptT κ (StateT σ Demonic) α) (y : α → ExceptT κ (StateT σ Demonic) β)
    (f : β → γ) : (x >>= fun a => f <$> y a) = f <$> (x >>= y) :=
  (map_bind _ _ _).symm

omit [DecidableEq κ] in
theorem throw_step (l : κ) :
    (throw l : ExceptT κ (StateT σ Demonic) (ForInStep PUnit))
      = ForInStep.done <$> (throw l : ExceptT κ (StateT σ Demonic) PUnit) := by
  rw [map_eq_pure_bind, throw_bind]

omit [DecidableEq κ] in
theorem forIn_map_done (x : ExceptT κ (StateT σ Demonic) PUnit) :
    FixLoop.mk.forIn PUnit.unit (fun _ _ => ForInStep.done <$> x) = x := by
  rw [FixLoop.forIn_eq, map_eq_pure_bind, bind_assoc]
  simp only [pure_bind]
  exact bind_pure_unit

omit [DecidableEq κ] in
theorem forIn_bind_throw {α β : Type} (b : β) (x : ExceptT κ (StateT σ Demonic) α) (l : κ) :
    FixLoop.mk.forIn b (fun _ _ => x >>= fun _ => (throw l : ExceptT κ (StateT σ Demonic) (ForInStep β)))
      = x >>= fun _ => throw l := by
  rw [FixLoop.forIn_eq, bind_assoc]
  simp only [throw_bind]

omit [DecidableEq κ] in
theorem forIn_throw {β : Type} (b : β) (l : κ) :
    FixLoop.mk.forIn b (fun _ _ => (throw l : ExceptT κ (StateT σ Demonic) (ForInStep β))) = throw l := by
  rw [FixLoop.forIn_eq, throw_bind]

/-! ## Termination

A state from which `cfgLoop` has a `wp` is accessible in the successor relation of the blocks: every
sequence of block runs from it ends. -/

/-- `y` follows `x`: the block at the label `x.1` runs from the state `x.2` and jumps to the label
`y.1` in the state `y.2`. -/
def CfgSucc (y x : κ × σ) : Prop :=
  stay x.2 = true ∧ ∃ b, T.get? x.1 = some b ∧ (b.run.run x.2).outs (.error y.1, y.2)

theorem acc_of_wp_cfgLoop {l : κ} {Q : Unit → σ → Prop} {E : (κ → σ → Prop) × EStack⟨⟩} {s : σ}
    (h : wp (cfgLoop stay T l) Q E s) : Acc (CfgSucc stay T) (l, s) := by
  have key : ∀ l Q E s, wp (cfgLoop stay T l) Q E s → Acc (CfgSucc stay T) (l, s) := by
    refine cfgLoop_induct stay T _ (admissible_wp_imp_fn fun l _ _ s => Acc (CfgSucc stay T) (l, s)) ?_
    intro f ih l Q E s hw
    refine Acc.intro _ fun y ⟨hs, b, hb, hy⟩ => ?_
    rw [wp_cfgStep_some stay T (hl := hb) (hs := hs), wp_run_eq] at hw
    have ht := (b.run.run s).mono (fun _ _ => trivial) hw
    exact ih y.1 Q E y.2 ((Demonic.wpD_iff ht _).mp hw _ hy)
  exact key l Q E s h

end

end Ascent
