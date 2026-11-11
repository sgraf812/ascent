import Demo.SwapL

/-!
# What `swap` computes

`swapL_spec` states, by `vcgen`, that the lifted `swap` exchanges the words at `p` and `q`: the
memory at the return is the memory with the word of `q` stored at `p`, then the word of `p` stored at
`q`.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

namespace Ascent.Kraken

theorem swapL_spec (p q : BitVec 64) (s₀ : MachineData) (m : DataMem)
    (hp : Mem.Mapped [(p, 8)] m) (hq : Mem.Mapped [(q, 8)] m)
    (hr : retAddrAt m (s₀.regs.get64 .rsp) = some s₀.retAddr.get!)
    (hpr : Mem.Blocks.Disjoint [(s₀.regs.get64 .rsp, 8)] [(p, 8)])
    (hqr : Mem.Blocks.Disjoint [(s₀.regs.get64 .rsp, 8)] [(q, 8)]) :
    ⦃(· = m)⦄ swapL p q s₀
      ⦃fun _ _ => False; (fun l m' => l = s₀.retAddr.get! ∧
        m' = Mem.storeInt (Mem.storeInt m p 8 (BitVec.ofInt 64 ((Mem.loadInt m q 8).get! % 2 ^ (8 * 8))).toInt)
          q 8 (BitVec.ofInt 64 ((Mem.loadInt m p 8).get! % 2 ^ (8 * 8))).toInt,
        estack⟨⟩)⦄ := by
  vcgen [swapL] with finish

section
variable [Host] [FunDecls] [Embeds swap] (s : MachineData) (ra : Int64)

theorem swap_refines_L {p q : BitVec 64}
    (hrdi : (s.push64 ra).regs.get64 .rdi = p) (hrsi : (s.push64 ra).regs.get64 .rsi = q) :
    ⦃(· = s.push64 ra)⦄ swap ⪯[(ofStateRepr abs).comp (ofStateRepr MachineData.dmem)]
      (swapL p q (s.push64 ra))
      ⦃fun _ _ _ => True; fun a l t => a = l ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        RegsRel [(.rbx, s.regs.get64 .rbx), (.rbp, s.regs.get64 .rbp), (.r12, s.regs.get64 .r12),
          (.r13, s.regs.get64 .r13), (.r14, s.regs.get64 .r14), (.r15, s.regs.get64 .r15)] t⦄ := by
  exact Refinement.comp_le (by grind) (by grind) (by grind)
    (swapL.refines p q (s.regs.get64 .rbx) (s.regs.get64 .rbp)
      (s.regs.get64 .r12) (s.regs.get64 .r13) (s.regs.get64 .r14) (s.regs.get64 .r15) (s.push64 ra))
    (swapT.refines (s.push64 ra))

theorem swap_correct {p q : BitVec 64}
    (hrdi : (s.push64 ra).regs.get64 .rdi = p) (hrsi : (s.push64 ra).regs.get64 .rsi = q)
    (hp : Mem.Mapped [(p, 8)] (s.push64 ra).dmem) (hq : Mem.Mapped [(q, 8)] (s.push64 ra).dmem)
    (hpr : Mem.Blocks.Disjoint [((s.push64 ra).regs.get64 .rsp, 8)] [(p, 8)])
    (hqr : Mem.Blocks.Disjoint [((s.push64 ra).regs.get64 .rsp, 8)] [(q, 8)]) :
    Triple swap (fun t => t = s.push64 ra) (fun _ _ => False)
      (fun a t => a = ra ∧ t.regs.get64 .rsp = s.regs.get64 .rsp ∧
        RegsRel [(.rbx, s.regs.get64 .rbx), (.rbp, s.regs.get64 .rbp), (.r12, s.regs.get64 .r12),
          (.r13, s.regs.get64 .r13), (.r14, s.regs.get64 .r14), (.r15, s.regs.get64 .r15)] t ∧
        t.dmem = Mem.storeInt (Mem.storeInt (s.push64 ra).dmem p 8
            (BitVec.ofInt 64 ((Mem.loadInt (s.push64 ra).dmem q 8).get! % 2 ^ (8 * 8))).toInt)
          q 8 (BitVec.ofInt 64 ((Mem.loadInt (s.push64 ra).dmem p 8).get! % 2 ^ (8 * 8))).toInt) := by
  have hr : retAddrAt (s.push64 ra).dmem ((s.push64 ra).regs.get64 .rsp) = some (s.push64 ra).retAddr.get! := by
    have h := MachineData.retAddr_push64 s ra
    rw [h, Option.get!_some]
    rw [MachineData.retAddr_eq] at h
    exact h
  have h := (swap_refines_L s ra hrdi hrsi).transport
    (swapL_spec p q (s.push64 ra) (s.push64 ra).dmem hp hq hr hpr hqr)
  refine ⟨fun t ht => WP.wp_monotone (x := swap) (fun _ _ h => by grind) ?_ t (h.le_wp t (by grind))⟩
  intro a t hE
  grind

end

section
variable [Host] [FunDecls]

/-! ## The call of a function

`Spec.call_of_correct` turns a correctness theorem of a callee, stated for every entry state
`s.push64 ra` and returning to `ra`, into the triple of a `call` of its label: the caller's
continuation must hold for every state that the callee's postcondition allows. -/

theorem Spec.call_of_correct {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g)
    (asz osz : Width) {Pre : MachineData → Prop} {Post : MachineData → MachineData → Prop}
    (hc : ∀ s ra, Pre s → Triple g.prog (fun t => t = s.push64 ra) (fun _ _ => False)
      (fun a t => a = ra ∧ Post s t)) {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃fun s => Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem ∧ Pre s ∧ ∀ t, Post s t → Q () t⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
      ⦃Q; E⦄ := by
  refine Triple.intro fun s ⟨hm, hpre, hq⟩ =>
    (Program.WP.Spec.call_label (f := f) (Q := Q) (E := E) asz osz).le_wp s ⟨hm, fun ra => ?_⟩
  rw [FunDecls.body_eq hg]
  refine WP.wp_monotone (x := g.prog) (fun _ _ h => h.elim) ?_ _ ((hc s ra hpre).le_wp _ rfl)
  intro a t ⟨hra, hpost⟩
  exact ⟨fun _ => hq t hpost, fun hne => absurd hra hne⟩

end

section
variable [Host] [FunDecls] [Embeds swap]

theorem swap_call (hs : FunDecls.at (label "_swap") = some ⟨swap⟩) (asz osz : Width)
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃fun s => Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
        ∧ (Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
          ∧ Mem.Mapped [(s.regs.get64 .rdi, 8)] s.dmem ∧ Mem.Mapped [(s.regs.get64 .rsi, 8)] s.dmem
          ∧ Mem.Blocks.Disjoint [(s.regs.get64 .rsp - 8#64, 8)] [(s.regs.get64 .rdi, 8)]
          ∧ Mem.Blocks.Disjoint [(s.regs.get64 .rsp - 8#64, 8)] [(s.regs.get64 .rsi, 8)])
        ∧ ∀ t, (t.regs.get64 .rsp = s.regs.get64 .rsp ∧
          RegsRel [(.rbx, s.regs.get64 .rbx), (.rbp, s.regs.get64 .rbp), (.r12, s.regs.get64 .r12),
            (.r13, s.regs.get64 .r13), (.r14, s.regs.get64 .r14), (.r15, s.regs.get64 .r15)] t ∧
          ∃ ra : Int64, t.dmem = Mem.storeInt (Mem.storeInt (s.push64 ra).dmem (s.regs.get64 .rdi) 8
              (BitVec.ofInt 64 ((Mem.loadInt (s.push64 ra).dmem (s.regs.get64 .rsi) 8).get! % 2 ^ (8 * 8))).toInt)
            (s.regs.get64 .rsi) 8
            (BitVec.ofInt 64 ((Mem.loadInt (s.push64 ra).dmem (s.regs.get64 .rdi) 8).get! % 2 ^ (8 * 8))).toInt)
          → Q () t⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label "_swap") .after_current_instruction)))))
      ⦃Q; E⦄ :=
  Spec.call_of_correct hs asz osz fun s ra hpre => by
    obtain ⟨hr, hp, hq, hpr, hqr⟩ := hpre
    have h := swap_correct s ra (p := s.regs.get64 .rdi) (q := s.regs.get64 .rsi) (by grind) (by grind)
      (by grind) (by grind) (by grind) (by grind)
    exact ⟨fun t ht => WP.wp_monotone (x := swap) (fun _ _ h => h) (fun a t' h => ⟨h.1, h.2.1, h.2.2.1, ra, h.2.2.2⟩) t
      (h.le_wp t ht)⟩

end

end Ascent.Kraken
