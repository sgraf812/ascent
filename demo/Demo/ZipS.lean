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

instance {x : BlockM σ α} {f : α → BlockM σ β} [hx : NoThrow x] [hf : ∀ a, NoThrow (f a)] :
    NoThrow (x >>= f) where
  noThrow s l s' h := by
    simp only [ExceptT.run_bind, StateT.run_bind] at h
    obtain ⟨⟨r, s₁⟩, h₁, h₂⟩ := (UB.bind_eq_some _ _ _).mp h
    rcases r with l₁ | a
    · exact hx.noThrow s l₁ s₁ h₁
    · exact (hf a).noThrow s₁ l s' h₂

instance (a : α) : NoThrow (Pure.pure a : BlockM σ α) where
  noThrow _ _ _ h := nomatch h

instance (g : σ → Prop) (f : σ → σ) : NoThrow (AInstr.modifyIf g f) where
  noThrow s l s' h := by
    rw [AInstr.modifyIf_run, AInstr.modifyIf] at h
    by_cases hg : g s
    · rw [UB.guardRet_of_pos hg] at h; nomatch h
    · rw [UB.guardRet_of_neg hg] at h; nomatch h

instance (g : σ → Prop) (f : σ → σ) : Exits (AInstr.exitIf g f .exit) where
  exits s l s' h := by
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
  modifyIf (loadOk8 .rsi .rax 0) (movRegSib8 .r8 .rsi .rax 0)
  modifyIf (loadOk8 .rdi .rax 0) (addRegSib8 .r8 .rdi .rax 0)
  modifyIf (storeOk8 .rdx .rax 0) (movSib8Reg .rdx .rax 0 .r8)
  modifyIf (fun _ => True) (incReg .rax)

/-- `zipWithAdd` as a structured loop over the machine state. -/
noncomputable def zipWithAddS : BlockM MachineData Unit := do
  let st ← get
  if CondCode.cmp .le (st.regs.get64 .rcx &&& st.regs.get64 .rcx) 0 then exitIf retOk ret .exit
  else
    modifyIf (fun _ => True) (xorReg32Reg32 .rax .rax)
    repeat'
      zipWithAddBody
      let st ← get
      if !(CondCode.cmp .nz (st.regs.get64 .rcx) (st.regs.get64 .rax)) then break
    exitIf retOk ret .exit

section
variable [Host] [FunDecls] [Embeds zipWithAdd]

theorem zipWithAddA_eq (s : MachineData) (ra : Int64) :
    zipWithAddA s ra = cfgLoop (Table.get [
      (.entry, branch (fun st => CondCode.cmp .le (st.regs.get64 .rcx &&& st.regs.get64 .rcx) 0)
        (.label "LBB0_3") >>= fun _ => modifyIf (fun _ => True) (xorReg32Reg32 .rax .rax)),
      (.label "LBB0_2", zipWithAddBody >>= fun _ =>
        branch (fun st => CondCode.cmp .nz (st.regs.get64 .rcx) (st.regs.get64 .rax)) (.label "LBB0_2")),
      (.label "LBB0_3", exitIf retOk ret .exit)]) (Program.next zipWithAdd) .entry := by
  have h₀ : zipWithAddA s ra = cfgLoop (Table.get [
      (.entry, do
        branch (fun st => CondCode.le.cmp (st.regs.get64 .rcx &&& st.regs.get64 .rcx) 0) (.label "LBB0_3")
        modifyIf (fun _ => True) (xorReg32Reg32 .rax .rax)
        pure ()),
      (.label "LBB0_2", do
        modifyIf (loadOk8 .rsi .rax 0) (movRegSib8 .r8 .rsi .rax 0)
        modifyIf (loadOk8 .rdi .rax 0) (addRegSib8 .r8 .rdi .rax 0)
        modifyIf (storeOk8 .rdx .rax 0) (movSib8Reg .rdx .rax 0 .r8)
        modifyIf (fun _ => True) (incReg .rax)
        branch (fun st => CondCode.nz.cmp (st.regs.get64 .rcx) (st.regs.get64 .rax)) (.label "LBB0_2")
        pure ()),
      (.label "LBB0_3", exitIf retOk ret .exit)]) (Program.next zipWithAdd) .entry := rfl
  rw [h₀]
  unfold zipWithAddBody
  simp only [bind_assoc, bind_pure_unit]

instance : NoThrow zipWithAddBody := by
  unfold zipWithAddBody; infer_instance

theorem zipWithAddA_refines_S (s : MachineData) (ra : Int64) :
    ⦃(⊤ : MachineData → Prop)⦄ (zipWithAddA s ra) ⪯[Concretization.ofStateRepr id] zipWithAddS
      ⦃fun _ _ _ => True; (fun l l' _ => l = l', estack⟨⟩)⦄ := by
  rw [zipWithAddA_eq]
  exact refines_cfgLoop_rotated (by simp) rfl rfl rfl

theorem wp_zipWithAddA_of_S (s : MachineData) (ra : Int64) (Qa : Unit → MachineData → Prop)
    (Ea : (CfgLabel → MachineData → Prop) × EStack⟨⟩) (t : MachineData)
    (h : wp zipWithAddS Qa Ea t) : wp (zipWithAddA s ra) Qa Ea t := by
  rw [zipWithAddA_eq]
  exact wp_cfgLoop_rotated Qa Ea (by simp) inferInstance inferInstance inferInstance rfl rfl rfl t h

end

end Ascent.Kraken
