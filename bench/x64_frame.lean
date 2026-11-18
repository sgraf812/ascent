import Driver
import CasesX64.Frame

/-! # `X64Frame`, engine measurements

The size `n` is the number of pushes, and of pops. The `sym_simp_def` step uses the rewrite rules of the
straight-line stack frame tests of the demo. -/

open Lean Meta Elab Std.WP Lean.Order Distillery DistillBench Distillery.Kraken Distillery.Kraken.AInstr
open DistillBench.X64Frame
open Distillery.Concretization (ofStateRepr)
open scoped Program.WP

set_option experimental.vcgen true

def mk (n : Nat) : MetaM Problem := return {
  binders := #[← `(bracketedBinder| [Host]), ← `(bracketedBinder| [FunDecls]),
    ← `(bracketedBinder| [Embeds (frame $(quote n) $(quote n))]),
    ← `(bracketedBinder| (r₀ : BitVec 64)), ← `(bracketedBinder| (ra : Int64))]
  stmt := ← `(⦃fun s => s.regs.get64 .rsp = r₀ ∧ s.retAddr = some ra⦄ (frame $(quote n) $(quote n))
    ⪯[ofStateRepr abs] (?_ : BlockM MachineData Unit) ⦃fun _ _ => ⊤; AddrRel r₀ ra⦄) }

def loopsPost : List Name := [``frame, ``pops, ``Program.loop, ``Program.entryNext,
  ``Program.firstLabel_nil, ``Program.firstLabel_cons, ``Program.table, ``Program.blocks_eq,
  ``List.filterMap_cons, ``List.filterMap_nil, ``List.reverse_nil, ``Table.get_cons,
  ``Option.some.injEq, ``reduceCtorEq, ``jumpTo_none, ``cfgLoop_eq_throw, ``Table.get?_nil,
  ``tryCatch_bind_assoc, ``tryCatch_modifyIf_bind, ``tryCatch_exitIf_cfgLoop, ``stayIn_setReg64_rsp,
  ``BitVec.reduceSLT, ``Bool.not_true, ``eq_self_iff_true, ``implies_true, ``bind_assoc,
  ``AInstr.exitIf_bind, ``bind_pure_unit, ``pure_bind]

def solve (n : Nat) (goal : MVarId) : MetaM (List MVarId) := do
  solveUsingTactic goal (← `(tactic| distill [refines_cfg (p := frame $(quote n) $(quote n)) (habs := abs_regs)]))

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

#eval runFamily "X64Frame" mk [] solve `(tactic| grind) [15, 30, 45]
  (symSimp? := some ([], loopsPost))
