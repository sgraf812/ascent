import Demo.Cfg

/-!
# Calls for every return address

`withRaOn ok push erase k` is the call of the abstract function `k` over a state `σ`. From the state
`s`, it runs `k s ra` from `push s ra` for every return address `ra`. An exit to `ra` is the return,
and `erase s` removes the return slot from the final state. If every `ra` gives the same outcome
and `ok s` holds, `withRaOn` has that outcome; otherwise it is undefined behaviour.

`withRaOn` never throws: if its outcome were an exit to `a`, the return address `ra = a` would turn
that exit into a return.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken.AInstr

namespace Ascent.Kraken

section
variable {σ : Type} (ok : σ → Prop) (push : σ → Int64 → σ) (erase : σ → σ → σ)
  (k : σ → Int64 → BlockM σ Unit)

/-- The outcome of the call from `s` for the return address `ra`, as the caller sees it. -/
noncomputable def callOutcomeOn (s : σ) (ra : Int64) : UB (Except Int64 Unit × σ) :=
  ((k s ra).run.run (push s ra)).bind fun
    | (.ok (), _) => none
    | (.error a, t) => some (if a = ra then .ok () else .error a, erase s t)

open Classical in
noncomputable def withRaOnRun (s : σ) : UB (Except Int64 Unit × σ) :=
  if ok s then
    if h : ∃ o, ∀ ra, callOutcomeOn push erase k s ra = o then Classical.choose h else UB.fail
  else UB.fail

/-- The call of the abstract function `k`. -/
noncomputable def withRaOn : BlockM σ Unit := ExceptT.mk fun s => withRaOnRun ok push erase k s

theorem withRaOn_run (s : σ) : (withRaOn ok push erase k).run.run s = withRaOnRun ok push erase k s := rfl

variable {ok push erase k}

theorem withRaOn_some {s : σ} {r : Except Int64 Unit × σ} (h : withRaOnRun ok push erase k s = some r) :
    ok s ∧ ∀ ra, callOutcomeOn push erase k s ra = some r := by
  unfold withRaOnRun at h
  by_cases hm : ok s
  · rw [if_pos hm] at h
    by_cases hex : ∃ o, ∀ ra, callOutcomeOn push erase k s ra = o
    · rw [dif_pos hex] at h
      refine ⟨hm, fun ra => ?_⟩
      rw [Classical.choose_spec hex ra, h]
    · rw [dif_neg hex] at h
      exact nomatch (h : (none : Option _) = some r)
  · rw [if_neg hm] at h
    exact nomatch (h : (none : Option _) = some r)

theorem withRaOn_eq_of {s : σ} {o : UB (Except Int64 Unit × σ)} (hm : ok s)
    (h : ∀ ra, callOutcomeOn push erase k s ra = o) : withRaOnRun ok push erase k s = o := by
  have hex : ∃ o, ∀ ra, callOutcomeOn push erase k s ra = o := ⟨o, h⟩
  unfold withRaOnRun
  rw [if_pos hm, dif_pos hex, ← Classical.choose_spec hex 0, h]

theorem callOutcomeOn_of_run {s : σ} {ra : Int64} {r : Except Int64 Unit × σ}
    (h : callOutcomeOn push erase k s ra = some r) :
    ∃ a t, (k s ra).run.run (push s ra) = some (.error a, t) ∧
      r = (if a = ra then .ok () else .error a, erase s t) := by
  unfold callOutcomeOn at h
  cases hr : (k s ra).run.run (push s ra) with
  | none => rw [hr] at h; exact nomatch h
  | some p =>
    rw [hr] at h
    obtain ⟨e, t⟩ := p
    cases e with
    | ok u => exact nomatch h
    | error a =>
      simp only [Option.bind_some] at h
      exact ⟨a, t, rfl, (Option.some.inj h).symm⟩

theorem withRaOnRun_ne_error {s t : σ} {a : Int64} : withRaOnRun ok push erase k s ≠ some (.error a, t) :=
  fun h => by
    obtain ⟨-, hall⟩ := withRaOn_some h
    obtain ⟨a', b, -, hr⟩ := callOutcomeOn_of_run (hall a)
    by_cases ha : a' = a
    · rw [if_pos ha] at hr
      exact nomatch (Prod.mk.inj hr).1
    · rw [if_neg ha] at hr
      injection (Prod.mk.inj hr).1 with h'
      exact ha h'.symm

theorem wp_withRaOn (Q : Unit → σ → Prop) (E E' : (Int64 → σ → Prop) × EStack⟨⟩) (s : σ) :
    wp (withRaOn ok push erase k) Q E s = wp (withRaOn ok push erase k) Q E' s := by
  rw [wp_BlockM_eq, wp_BlockM_eq, withRaOn_run]
  cases h : withRaOnRun ok push erase k s with
  | none => rfl
  | some r =>
    obtain ⟨e, t⟩ := r
    cases e with
    | ok u => rfl
    | error a => exact absurd h withRaOnRun_ne_error

theorem ThrowsOnly.withRaOn {P : Int64 → σ → Prop} :
    Ascent.ThrowsOnly P (withRaOn ok push erase k) = True := eq_true fun Q E s hw => by
  rw [wp_withRaOn Q _ E s]
  exact hw

theorem tryCatch_withRaOn_bind {β : Type} (f : Unit → BlockM σ β) (h : Int64 → BlockM σ β) :
    tryCatch (withRaOn ok push erase k >>= f) h = withRaOn ok push erase k >>= fun u => tryCatch (f u) h := by
  have hmono : ∀ (Q : β → σ → Prop) (E : (Int64 → σ → Prop) × EStack⟨⟩) u t,
      wp (f u) Q (fun l => wp (h l) Q E, E.2) t ↔ wp (tryCatch (f u) h) Q E t :=
    fun Q E u t => by rw [BlockLoop.wp_tryCatch]
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [BlockLoop.wp_tryCatch, WPMonadExact.wp_bind_eq] at hw ⊢
  · rw [wp_withRaOn _ _ E s] at hw
    exact WP.wp_monotone_post (x := withRaOn ok push erase k) (fun u t h' => (hmono Q E u t).mp h') s hw
  · rw [wp_withRaOn _ _ (fun l => wp (h l) Q E, E.2) s]
    rw [wp_withRaOn _ _ (fun l => wp (h l) Q E, E.2) s] at hw
    exact WP.wp_monotone_post (x := withRaOn ok push erase k) (fun u t h' => (hmono Q E u t).mpr h') s hw

end

end Ascent.Kraken
