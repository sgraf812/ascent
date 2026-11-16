import Demo.L1Gen

/-!
# Calls

A call pushes the return address, runs the callee, and continues when the callee returns to that
address. The return address is the end address of the call instruction in the embedding of the
program, which the abstract program cannot know. `callA k` therefore pushes an unknown word `v`
(`pushUnknown`) and runs the abstract callee `k (r - 8) v` with `v` as its return address. The
callee returns by throwing `v`, as every function of this development does with its parameter `ra`
(`wrp_ret`, `AddrRel`), and the caller continues if the thrown label is `v` and the stack pointer
is back at `r`. The refinement of a call instantiates `v` with the actual return address, so the
abstract state equals the concrete one, return slot included.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr ofStateRel ofStateRepr_pred ofStateRel_pred)
open scoped Program.WP

namespace Ascent.Kraken

/-- Push an unknown 8-byte word below the stack pointer and return it. -/
def pushUnknown : BlockM MachineData Int64 :=
  ExceptT.mk fun s => do
    Demonic.assert ((Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true)
    let v ← (Demonic.unknown : Demonic Int64)
    pure (.ok v, s.push64 v)

theorem wp_pushUnknown_fun (Q : Int64 → MachineData → Prop)
    (E : (Int64 → MachineData → Prop) × EStack⟨⟩) :
    wp pushUnknown Q E = fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true ∧
      ∀ v, Q v (s.push64 v) :=
  funext fun _ => propext ⟨fun ⟨hm, h⟩ => ⟨hm, fun v => h v trivial⟩, fun ⟨hm, h⟩ => ⟨hm, fun v _ => h v⟩⟩

noncomputable def callA (k : BitVec 64 → Int64 → BlockM MachineData Unit) : BlockM MachineData Unit := do
  let r ← peek fun s => s.regs.get64 .rsp
  let v ← pushUnknown
  tryCatch (do k (r - 8#64) v; modifyIf (fun _ => False) id) fun l =>
    modifyIf (fun s => l = v ∧ s.regs.get64 .rsp = r) id

theorem wp_modifyIf_fun {σ : Type} (g : σ → Prop) (f : σ → σ) (Q : Unit → σ → Prop)
    (E : (Int64 → σ → Prop) × EStack⟨⟩) : wp (modifyIf g f) Q E = fun s => g s ∧ Q () (f s) :=
  funext fun s => wp_modifyIf Q E s g f

theorem wp_tryCatch_fun {σ α : Type} (x : BlockM σ α) (h : Int64 → BlockM σ α) (Q : α → σ → Prop)
    (E : (Int64 → σ → Prop) × EStack⟨⟩) : wp (tryCatch x h) Q E = wp x Q (fun l => wp (h l) Q E, E.2) :=
  funext fun s => BlockLoop.wp_tryCatch x h Q E s

theorem ThrowsOnly.callA {P : Int64 → MachineData → Prop} (k : BitVec 64 → Int64 → BlockM MachineData Unit) :
    Ascent.ThrowsOnly P (callA k) = True := eq_true fun Q E s hw => by
  simp only [Kraken.callA, WPMonadExact.wp_bind_eq, wp_peek, wp_pushUnknown_fun, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun] at hw ⊢
  exact hw

theorem tryCatch_callA_bind {β : Type} (k : BitVec 64 → Int64 → BlockM MachineData Unit)
    (f : Unit → BlockM MachineData β) (h : Int64 → BlockM MachineData β) :
    tryCatch (callA k >>= f) h = callA k >>= fun u => tryCatch (f u) h := by
  apply BlockLoop.ext_wp <;> intro Q E s hw <;>
    simp only [Kraken.callA, WPMonadExact.wp_bind_eq, wp_peek, wp_pushUnknown_fun, BlockLoop.wp_tryCatch,
      wp_modifyIf_fun, wp_tryCatch_fun] at hw ⊢ <;>
    exact hw

theorem abs_push64 (s : MachineData) (v : Int64) : abs (s.push64 v) = (abs s).push64 v := rfl

attribute [vcgen_simp] MachineData.regs_push64

section
variable [Host] [FunDecls]

@[ascend] theorem wrp_call {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g)
    (asz osz : Width) {k : BitVec 64 → Int64 → BlockM MachineData Unit}
    (hk : ∀ (r : BitVec 64) (ra : Int64),
      ⦃fun s => s.regs.get64 .rsp = r ∧ s.retAddr = some ra⦄ g.prog ⪯[ofStateRepr abs] (k r ra)
        ⦃fun _ _ => ⊤; AddrRel r ra⦄)
    {Q : Unit → Unit → MachineData → Prop} {E : Int64 → Int64 → MachineData → Prop} :
    (fun _ => ∀ t, Q () () t)
      ⊑ wrp (ofStateRepr abs)
          (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
          (callA k) Q E := by
  refine wrp_intro fun Qa Ea => ?_
  intro s hs
  simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred] at hs
  obtain ⟨hQ, hw⟩ := hs
  simp only [callA, WPMonadExact.wp_bind_eq, wp_peek, wp_pushUnknown_fun, BlockLoop.wp_tryCatch,
    wp_modifyIf_fun] at hw
  obtain ⟨hm, hw⟩ := hw
  refine (Program.WP.wp_call_iff hg).mpr fun [h : Embeds _] => ?_
  let ra := h.embedding.endAddr
  refine ⟨by simpa only [abs_regs, abs_dmem] using hm, ?_⟩
  rw [FunDecls.body_eq hg]
  let Qa' : Unit → MachineData → Prop := fun _ _ => False
  let Ea' : (Int64 → MachineData → Prop) × EStack⟨⟩ :=
    (fun l b => (l = ra ∧ b.regs.get64 .rsp = s.regs.get64 .rsp) ∧ Qa () b, estack⟨⟩)
  have hwk : wp (k (s.regs.get64 .rsp - 8#64) ra) Qa' Ea' (abs (s.push64 ra)) := by
    rw [abs_push64]
    refine WP.wp_monotone (x := k (s.regs.get64 .rsp - 8#64) ra) ?_ ?_ _ (hw ra)
    · intro u t ht
      exact ht.1
    · refine Prod.mk_le _ _ _ ?_ PartialOrder.rel_refl
      intro l t ht
      exact ht
  have hc := wrp_transport (hk (s.regs.get64 .rsp - 8#64) ra).le_wrp Qa' Ea' (s.push64 ra)
    (by
      simp only [meet_apply, meet_prop_eq_and, ofStateRepr_pred]
      exact ⟨⟨by simp only [MachineData.regs_push64, Reg64s.get64_set64, ↓reduceIte],
        MachineData.retAddr_push64 s ra⟩, hwk⟩)
  refine Program.wp_mono (fun u hu => ?_) (fun u hu => ?_) hc
  · simp only [Concretization.post_pi, ofStateRepr_pred, Qa', and_false, exists_false] at hu
  · simp only [ePosts_ret, Concretization.post_pi, ofStateRepr_pred, AddrRel_eq] at hu
    obtain ⟨l, hl, ⟨hlr, hrsp⟩, hqa⟩ := hu
    subst hl
    rw [if_pos hlr]
    simp only [Concretization.post_pi, ofStateRepr_pred]
    exact ⟨(), hQ _, hqa⟩

end

end Ascent.Kraken
