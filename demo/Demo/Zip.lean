import Demo.AState
import Kraken.X64.Parser
import Ascent.Tactic.VCGen.Frontend

/-!
# `zipWithAdd`

The x64 text that clang emits for

```c
void zipWithAdd(const long *a, const long *b, long *out, long n) {
  for (long i = 0; i < n; i++)
    out[i] = a[i] + b[i];
}
```

with `-O1 -fno-vectorize -fno-unroll-loops`, and its refinement to the abstract machine.
-/

open Kraken.X64.Parser Std.WP Lean.Order Ascent Ascent.Kraken Ascent.Kraken.AInstr
open Ascent.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

def zipWithAdd : Program := parse("
  testq %rcx, %rcx
  jle LBB0_3
  xorl %eax, %eax
LBB0_2:
  movq (%rsi,%rax,8), %r8
  addq (%rdi,%rax,8), %r8
  movq %r8, (%rdx,%rax,8)
  incq %rax
  cmpq %rax, %rcx
  jne LBB0_2
LBB0_3:
  retq
")

/-- The relation VCs of a block: an internal jump, a fallthrough, or the return. -/
macro "cfg_vc" : tactic => `(tactic| (
  first
  | refine JumpRel.internal (by decide) rfl (StackOf.of_step (by assumption) ?_ ?_)
  | refine FallRel.intro (StackOf.of_step (by assumption) ?_ ?_)
  | refine JumpRel.exit (by rw [(‹StackOf _ _›).2]) ?_
  all_goals first
  | rfl
  | (have h := ‹sib8Storable _ _ _ _ = true›
     simp only [sib8Storable_eq, sib8Loaded_eq, AState.frameSafe, AState.sib8, abs_regs, abs_mem,
       Reg64s.get64, Bool.and_eq_true, decide_eq_true_eq, Int64.toInt_zero, BitVec.ofInt_ofNat,
       BitVec.add_zero] at h
     exact Mem.loadInt_storeInt_of_disjoint (Mem.Blocks.Disjoint.of_sub h.2.1 h.2.2) _)
  | (have h1 := (‹StackOf _ _›).1
     simp only [Reg64s.get64, Reg64s.get64_set64] at h1 ⊢
     rw [h1])))

/-- The block table of `zipWithAdd`, one abstract block per label. -/
def table (b₀ b₁ b₂ : BlockM AState Unit) : CfgLabel → BlockM AState Unit
  | .entry => b₀
  | .label "LBB0_2" => b₁
  | .label "LBB0_3" => b₂
  | _ => pure ()

noncomputable def zipWithAddA [Host] [FunDecls] (s : MachineData) (ra : Int64) :
    { a : BlockM AState Unit //
      wrp (ofStateRepr abs) zipWithAdd a (fun _ _ => ⊤) (RetRel s ra) (s.push64 ra) } := by
  refine ⟨cfgLoop (table ?b₀ ?b₁ ?b₂) (Program.next zipWithAdd) .entry, ?prop⟩
  case prop =>
    refine wrp_cfg (p := zipWithAdd) abs (Program.next zipWithAdd) (by decide) ?_
    simp only [Program.blocks_eq, zipWithAdd, Program.view_cons_instr, Program.view_cons_label,
      Program.view_nil', Program.blocksFrom_cons, Program.blocksFrom_nil, List.forall_mem_cons,
      table]
    refine ⟨?_, ?_, ?_, List.forall_mem_nil _⟩
    all_goals intro t hst
    all_goals ascend
    all_goals cfg_vc

/-- The synthesized L1 program: the text over the abstract machine, block by block. -/
example [Host] [FunDecls] (s : MachineData) (ra : Int64) :
    (zipWithAddA s ra).1 = cfgLoop (table
      (do
        testRegReg .rcx .rcx
        jcc .le "LBB0_3"
        xorReg32Reg32 .rax .rax
        pure ())
      (do
        movRegSib8 .r8 .rsi .rax 0
        addRegSib8 .r8 .rdi .rax 0
        movSib8Reg .rdx .rax 0 .r8
        incReg .rax
        cmpRegReg .rcx .rax
        jcc .nz "LBB0_2"
        pure ())
      ret) (Program.next zipWithAdd) .entry := rfl
