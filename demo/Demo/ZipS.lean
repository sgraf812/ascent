import Demo.Zip
import Demo.Structure

/-!
# `zipWithAdd` as a structured loop

`zipWithAddS` is the first layer of `zipWithAdd` with the block loop turned into a `repeat'` loop by
`wp_cfgLoop_rotated`. The test `testq %rcx, %rcx; jle LBB0_3` becomes the `if`, and the back jump
`cmpq %rax, %rcx; jne LBB0_2` becomes the `break` condition.
-/

open Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr

namespace Ascent.Kraken

/-! ## Block programs that throw no label -/

section
variable {σ α β : Type}

theorem NoThrow.bind {x : BlockM σ α} {f : α → BlockM σ β} (hx : NoThrow x)
    (hf : ∀ a, NoThrow (f a)) : NoThrow (x >>= f) := by
  intro s l s' h
  simp only [ExceptT.run_bind, StateT.run_bind] at h
  obtain ⟨⟨r, s₁⟩, h₁, h₂⟩ := (UB.bind_eq_some _ _ _).mp h
  rcases r with l₁ | a
  · exact hx s l₁ s₁ h₁
  · exact hf a s₁ l s' h₂

theorem NoThrow.pure (a : α) : NoThrow (Pure.pure a : BlockM σ α) := fun _ _ _ h => nomatch h

theorem NoThrow.modifyIf (g : σ → Prop) (f : σ → σ) : NoThrow (modifyIf g f) := by
  intro s l s' h
  rw [AInstr.modifyIf_run, AInstr.modifyIf] at h
  by_cases hg : g s
  · rw [UB.guardRet_of_pos hg] at h; nomatch h
  · rw [UB.guardRet_of_neg hg] at h; nomatch h

theorem Exits.exitIf (g : σ → Prop) (f : σ → σ) : Exits (exitIf g f .exit) := by
  intro s l s' h
  rw [AInstr.exitIf_run, AInstr.exitIf] at h
  by_cases hg : g s
  · rw [UB.guardRet_of_pos hg] at h
    cases h
    rfl
  · rw [UB.guardRet_of_neg hg] at h; nomatch h

end

/-! ## The structured program -/

/-- The body of the loop of `zipWithAdd`, without its back jump. -/
noncomputable def zipWithAddBody : BlockM MachineData Unit := do
  movRegSib8 .r8 .rsi .rax 0
  addRegSib8 .r8 .rdi .rax 0
  movSib8Reg .rdx .rax 0 .r8
  incReg .rax

/-- `zipWithAdd` as a structured loop over the machine state. -/
noncomputable def zipWithAddS : BlockM MachineData Unit := do
  let st ← get
  if CondCode.cmp .le (st.regs.get64 .rcx &&& st.regs.get64 .rcx) 0 then ret
  else
    xorReg32Reg32 .rax .rax
    repeat'
      zipWithAddBody
      let st ← get
      if !(CondCode.cmp .nz (st.regs.get64 .rcx) (st.regs.get64 .rax)) then break
    ret

section
variable [Host] [FunDecls] [Embeds zipWithAdd]

theorem zipWithAddA_eq (s : MachineData) (ra : Int64) :
    zipWithAddA s ra = cfgLoop (Table.get [
      (.entry, branch (fun st => CondCode.cmp .le (st.regs.get64 .rcx &&& st.regs.get64 .rcx) 0)
        (.label "LBB0_3") >>= fun _ => xorReg32Reg32 .rax .rax),
      (.label "LBB0_2", zipWithAddBody >>= fun _ =>
        branch (fun st => CondCode.cmp .nz (st.regs.get64 .rcx) (st.regs.get64 .rax)) (.label "LBB0_2")),
      (.label "LBB0_3", ret)]) (Program.next zipWithAdd) .entry := by
  have h₀ : zipWithAddA s ra = cfgLoop (Table.get [
      (.entry, do
        testJcc .rcx .rcx .le "LBB0_3"
        xorReg32Reg32 .rax .rax
        pure ()),
      (.label "LBB0_2", do
        movRegSib8 .r8 .rsi .rax 0
        addRegSib8 .r8 .rdi .rax 0
        movSib8Reg .rdx .rax 0 .r8
        incReg .rax
        cmpJcc .rcx .rax .nz "LBB0_2"
        pure ()),
      (.label "LBB0_3", ret)]) (Program.next zipWithAdd) .entry := rfl
  rw [h₀]
  unfold zipWithAddBody
  simp only [bind_assoc, bind_pure_unit, testJcc, cmpJcc]

theorem zipWithAddBody_noThrow : NoThrow zipWithAddBody := by
  unfold zipWithAddBody
  exact NoThrow.bind (NoThrow.modifyIf _ _) fun _ => NoThrow.bind (NoThrow.modifyIf _ _) fun _ =>
    NoThrow.bind (NoThrow.modifyIf _ _) fun _ => NoThrow.modifyIf _ _

theorem zipWithAddA_refines_S (s : MachineData) (ra : Int64) :
    ⦃(⊤ : MachineData → Prop)⦄ (zipWithAddA s ra) ⪯[Concretization.ofStateRepr id] zipWithAddS
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ := by
  rw [zipWithAddA_eq]
  exact refines_cfgLoop_rotated (by simp) (NoThrow.modifyIf _ _) zipWithAddBody_noThrow
    (Exits.exitIf _ _) rfl rfl rfl

theorem wp_zipWithAddA_of_S (s : MachineData) (ra : Int64) (Qa : Unit → MachineData → Prop)
    (Ea : (CfgLabel → MachineData → Prop) × EStack⟨⟩) (t : MachineData)
    (h : wp zipWithAddS Qa Ea t) : wp (zipWithAddA s ra) Qa Ea t := by
  rw [zipWithAddA_eq]
  exact wp_cfgLoop_rotated Qa Ea (by simp) (NoThrow.modifyIf _ _) zipWithAddBody_noThrow
    (Exits.exitIf _ _) rfl rfl rfl t h

end

end Ascent.Kraken
