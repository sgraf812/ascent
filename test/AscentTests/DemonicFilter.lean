import Ascent.Demonic

/-!
# A non-principal element of `Demonic`

`eventually` returns any large enough natural number: its filter is the Fréchet filter on `Nat`.
`eventually` is no `select p`, its outcome set `Demonic.Internal.outs eventually` is empty, and the
`wp` of `Demonic Nat` preserves no infinite meet.
-/

open Std.WP Lean.Order Ascent

namespace Ascent.DemonicFilterTests

def eventually : Demonic Nat :=
  Demonic.selectFilter (fun Q => ∃ n, ∀ m, n ≤ m → Q m)
    (fun h ⟨n, hn⟩ => ⟨n, fun m hm => h m (hn m hm)⟩)
    (fun ⟨n, hn⟩ ⟨n', hn'⟩ => ⟨max n n', fun m hm =>
      ⟨hn m (Nat.le_trans (Nat.le_max_left _ _) hm), hn' m (Nat.le_trans (Nat.le_max_right _ _) hm)⟩⟩)

theorem eventually_ne (k : Nat) : eventually.wpD (· ≠ k) :=
  ⟨k + 1, fun _ hm he => by subst he; exact Nat.not_succ_le_self _ hm⟩

theorem not_eventually_false : ¬eventually.wpD fun _ => False :=
  fun ⟨n, hn⟩ => hn n (Nat.le_refl n)

theorem outs_eventually (a : Nat) : ¬Demonic.Internal.outs eventually a :=
  fun h => h _ (eventually_ne a) rfl

theorem eventually_ne_select (p : Nat → Prop) : eventually ≠ Demonic.select p := fun h =>
  not_eventually_false (h ▸ fun a hp => (h ▸ eventually_ne a : (Demonic.select p).wpD (· ≠ a)) a hp rfl)

theorem not_wpD_outs : ¬eventually.wpD (Demonic.Internal.outs eventually) :=
  fun h => not_eventually_false (eventually.mono (fun a ha => outs_eventually a ha) h)

theorem not_infConjunctive :
    ¬(iInf (fun k : ULift Nat => wp eventually (fun a => a ≠ k.down) estack⟨⟩)
      ⊑ wp eventually (iInf fun (k : ULift Nat) (a : Nat) => a ≠ k.down) estack⟨⟩) := fun this => by
  rw [iInf_prop_eq_forall] at this
  have hall := this fun k => eventually_ne k.down
  have hQ : iInf (fun (k : ULift Nat) (a : Nat) => a ≠ k.down) = fun _ => False :=
    funext fun a => by
      rw [iInf_apply, iInf_prop_eq_forall]
      exact propext ⟨fun h => h ⟨a⟩ rfl, False.elim⟩
  rw [hQ] at hall
  exact not_eventually_false hall

end Ascent.DemonicFilterTests
