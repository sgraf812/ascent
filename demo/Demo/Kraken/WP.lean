import Demo.Kraken.Machine
import Demo.Kraken.Blocks
import Std.WP
import Std.Tactic.Do

/-!
# The weakest precondition of a text

The declarations of this module mirror the exported API of kraken's `Kraken.X64.WP`,
`Kraken.X64.WP.Spec`, `Kraken.X64.WP.Step`, `Kraken.X64.Inert`, `Kraken.KVCGen` and of the semantic
part of `Kraken.StateCfg`, under kraken's names. The host program, its embeddings and its function
declarations are structures and classes, because the demo builds them. `Program.wp` and the other
operations are opaque, and the axioms state kraken's theorems about them. The `WP` instances of
texts and directives are kraken's instances, built from `Program.wp`.

These axioms are not theorems of kraken:

* `List.isInfixAt_def`, `Host.exe_def`, `Host.addrOf_def`, `While_def`,
  `Program.internalTarget_def`, `Embedding.startAddr_def`, `Embedding.endAddr_def`,
  `Executable.stepIn_def`, `Executable.stepOver_def`, `Executable.stepOut_of_none`,
  `BitVec.serialLt_def`, `MachineData.stackBelow_def`, `MachineData.stackAtOrBelow_def`,
  `Program.continueOnInternalExit_def` and `MachineData.push64_def` state kraken's definitions.
* `Directive.inert_label` states that a label is inert.
* The specs `Program.WP.Spec.movzx_reg32_sib1`, `movzx_reg32_mem1`, `mov_sib1_reg8`, `mov_reg_mem`,
  `sub_reg_reg`, `shr_reg_one`, `mov_reg8_imm`, `test_reg8_reg8`, `push_reg16`, `pop_reg16`,
  `lea_reg_sib`, `lea_reg_base_disp` and `mov_reg32_imm` state the semantics of instructions that
  kraken has no spec for.
-/

open Std.WP Lean.Order

universe u

opaque List.IsInfixAt {α : Type u} (l₁ l₂ : List α) (k : Nat) : Prop

axiom List.isInfixAt_def {α : Type u} (l₁ l₂ : List α) (k : Nat) :
    l₁.IsInfixAt l₂ k = l₁.IsPrefix (l₂.drop k)

axiom List.isInfixAt_iff_getElem? {α : Type u} {l₁ l₂ : List α} {k : Nat} :
    l₁.IsInfixAt l₂ k ↔ ∀ i (h : i < l₁.length), l₂[k + i]? = some l₁[i]

abbrev Post {State : Type} := State → Prop

inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

inductive Instr.IsPadding : Instr → Prop
  | nop {asz osz : Width} {n : Nat} : Instr.IsPadding (.regular asz osz (.nop n))
  | nopalign {asz osz : Width} {a : Nat} {p : Option Nat} : Instr.IsPadding (.regular asz osz (.nopalign a p))

opaque Directive.Inert (d : Directive) : Prop

axiom Directive.inert_label (l : Label) : (Directive.label l).Inert

class Host where
  prog : Program
  layout : Layout
  labels_nodup : (Program.labels prog).Nodup
  label_size : ∀ i l, prog[i]? = some (.label l) → @Kraken.Layout.size _ layout i = 0
  instr_size_pos : ∀ i ins, prog[i]? = some (.instr ins) → ¬ ins.IsPadding → 0 < @Kraken.Layout.size _ layout i
  instr_addr_ne : ∀ i ins, prog[i]? = some (.instr ins) → (layout.apply prog).addrOf i ≠ -1
  zero_inert : ∀ i d, prog[i]? = some d → @Kraken.Layout.size _ layout i = 0 → d.Inert
  addr_determines_offset : ∀ j k, (layout.apply prog).addrOf j = (layout.apply prog).addrOf k →
    (layout.apply prog).sizeBefore j = (layout.apply prog).sizeBefore k

instance [Host] : Layout := Host.layout

opaque Host.exe [Host] : Executable

axiom Host.exe_def [Host] : Host.exe = Host.layout.apply Host.prog

opaque Host.addrOf [Host] (k : Nat) : Int64

axiom Host.addrOf_def [Host] (k : Nat) : Host.addrOf k = Host.exe.addrOf k

instance [Host] : Labels := Executable.labels Host.exe

axiom Host.exe_getElem? [Host] (i : Nat) :
    Host.exe.program[i]? = Host.prog[i]?.map (fun d => {directive := d, size := Kraken.Layout.size Directive i})

axiom Host.addrOf_succ [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Kraken.Layout.size Directive k)

axiom Host.inert_of_size_zero [Host] {d : Directive} (h : {directive := d, size := 0} ∈ Host.exe.program) :
    d.Inert

axiom Host.label_eq [Host] {p : Program} {k i : Nat} {l : Label}
    (hp : p.IsInfixAt Host.prog k) (hi : p[i]? = some (.label l)) :
    label l = Host.addrOf (k + i)

axiom Host.label_ne [Host] {p : Program} {k : Nat} (i j : Nat) {l l' : Label} {ins : Instr}
    (hp : p.IsInfixAt Host.prog k) (hij : i < j := by omega)
    (hi : p[i]? = some (.label l) := by rfl) (hi1 : p[i + 1]? = some (.instr ins) := by rfl)
    (hj : p[j]? = some (.label l') := by rfl) (hpad : ¬ ins.IsPadding := by nofun) :
    label l ≠ label l'

axiom Host.interp_addrOf [Host] {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) (s : MachineData)
    (ret jmp : MachineState → Effects) (P : MachineState → Prop) :
    (@Directives.interp Host.exe.labels (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k)
        (fun a s => ret ⟨s, a⟩) (fun a s => jmp ⟨s, a⟩)).All P ↔
      (c.directive.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩ (fun s' => ret ⟨s', Host.addrOf (k + 1)⟩)
        (fun a s' => jmp ⟨s', a⟩)).All P

axiom Directives.interp_inert_append [Labels] {pre rest : List (Kraken.Sized Directive)}
    (hpre : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert) (s : MachineData) (pc : Int64)
    (ret : Int64 → MachineData → Effects) (post : @Post MachineState)
    (jmp : Int64 → MachineData → Effects := ret) :
    (Directives.interp (pre ++ rest) s pc ret jmp).All post ↔ (Directives.interp rest s pc ret jmp).All post

/-! ## Loops -/

opaque While {σ : Type} (cond : σ → Prop) (body : (σ → Prop) → σ → Prop) (done : σ → Prop) :
    σ → Prop

axiom While_def {σ : Type} (cond : σ → Prop) (body : (σ → Prop) → σ → Prop) (done : σ → Prop) :
    While cond body done =
      Eventually (fun st «continue» => cond st ∧ body «continue» st) (fun st => ¬ cond st ∧ done st)

section
variable {σ : Type} {cond : σ → Prop} {body : (σ → Prop) → σ → Prop} {done : σ → Prop}

axiom While.stop {x : σ} (hc : ¬ cond x) (hd : done x) : While cond body done x

axiom While.imp {body₂ : (σ → Prop) → σ → Prop} {done₂ : σ → Prop}
    (hb : ∀ U y, cond y → body U y → body₂ U y) (hd : ∀ y, ¬ cond y → done y → done₂ y) {x : σ}
    (h : While cond body done x) : While cond body₂ done₂ x

end

/-! ## Embeddings and function declarations -/

structure Embedding [Host] (p : Program) where
  start : Nat
  isInfixAt : p.IsInfixAt Host.prog start

class Embeds [Host] (p : Program) where
  embedding : Embedding p

opaque Program.InternalTarget [Host] (p : Program) (a : Int64) : Prop

axiom Program.internalTarget_def [Host] (p : Program) (a : Int64) :
    p.InternalTarget a = ∃ l ∈ p.labels, label l = a

structure Fragment [Host] where
  prog : Program
  [embeds : Embeds prog]

section
variable [Host]

opaque Embedding.startAddr {p : Program} (e : Embedding p) : Int64

opaque Embedding.endAddr {p : Program} (e : Embedding p) : Int64

axiom Embedding.startAddr_def {p : Program} (e : Embedding p) : e.startAddr = Host.addrOf e.start

axiom Embedding.endAddr_def {p : Program} (e : Embedding p) :
    e.endAddr = Host.addrOf (e.start + p.length)

end

class FunDecls [Host] where
  funs : List Fragment

instance [Host] : FunDecls := ⟨[]⟩

opaque FunDecls.at [Host] [FunDecls] (a : Int64) : Option Fragment

@[simp] axiom FunDecls.at_default [Host] (a : Int64) :
    (FunDecls.at a : Option Fragment) = none

/-! ## Steps -/

opaque Executable.StepIn (e : Executable) (next jump : MachineState → Prop) (st : MachineState) : Prop

axiom Executable.stepIn_def (e : Executable) (next jump : MachineState → Prop) (st : MachineState) :
    e.StepIn next jump st =
      let := e.labels
      ∀ ⦃P : MachineState → Prop⦄ ⦃ret jmp : MachineState → Effects⦄,
        (∀ st', next st' → (ret st').All P) → (∀ st', jump st' → (jmp st').All P) →
          (Directives.interp (e.directivesAtAddress st.pc) st.data st.pc (fun a s => ret ⟨s, a⟩)
            (fun a s => jmp ⟨s, a⟩)).All P

opaque BitVec.SerialLt {w : Nat} (a b : BitVec w) : Prop

opaque MachineData.StackBelow (s' s : MachineData) : Prop

opaque MachineData.StackAtOrBelow (s' s : MachineData) : Prop

axiom BitVec.serialLt_def {w : Nat} (a b : BitVec w) : a.SerialLt b = (0 < (b - a).toInt)

axiom MachineData.stackBelow_def (s' s : MachineData) :
    s'.StackBelow s = (s'.regs.get64 .rsp).SerialLt (s.regs.get64 .rsp)

axiom MachineData.stackAtOrBelow_def (s' s : MachineData) : s'.StackAtOrBelow s = ¬ s.StackBelow s'

opaque Executable.StepOut (e : Executable)
    (callee : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (st : MachineState) (next jump : MachineState → Prop) (st' : MachineState) : Prop

axiom Executable.stepOut_of_none (e : Executable)
    {callee : Int64 → Option ((MachineState → Prop) → MachineData → Prop)}
    (st : MachineState) (next jump : MachineState → Prop) (st' : MachineState)
    (h : callee st'.pc = none) : e.StepOut callee st next jump st' = jump st'

opaque Executable.StepOver (e : Executable)
    (callee : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (next jump : MachineState → Prop) (st : MachineState) : Prop

axiom Executable.stepOver_def (e : Executable)
    (callee : Int64 → Option ((MachineState → Prop) → MachineData → Prop))
    (next jump : MachineState → Prop) (st : MachineState) :
    e.StepOver callee next jump st = e.StepIn next (e.StepOut callee st next jump) st

opaque Program.ContinueOnInternalExit [Host] (p : Program) (s : MachineData)
    («continue» exit : MachineState → Prop) (st : MachineState) : Prop

open Classical in
axiom Program.continueOnInternalExit_def [Host] (p : Program) (s : MachineData)
    («continue» exit : MachineState → Prop) (st : MachineState) :
    p.ContinueOnInternalExit s «continue» exit st =
      if p.InternalTarget st.pc ∧ st.data.StackAtOrBelow s then «continue» st else exit st

/-! ## The weakest precondition -/

opaque Program.wp [Host] [FunDecls] (p : Program) (done exit : MachineState → Prop)
    (s : MachineData) : Prop

section
variable [Host] [FunDecls]

axiom Program.wp_eq {p : Program} {done exit : MachineState → Prop} {s : MachineData} :
    p.wp done exit s = ∀ [h : Embeds p], While (·.pc ≠ h.embedding.endAddr)
      (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        «continue» (p.ContinueOnInternalExit s «continue» exit))
      done ⟨s, h.embedding.startAddr⟩

axiom Program.wp_mono {p : Program} {done₁ done₂ exit₁ exit₂ : MachineState → Prop}
    (hd : ∀ u, done₁ u → done₂ u) (he : ∀ u, exit₁ u → exit₂ u) {s : MachineData}
    (h : p.wp done₁ exit₁ s) : p.wp done₂ exit₂ s

axiom Program.wp_cons {d : Directive} {p : Program} {done exit : MachineState → Prop} {s : MachineData}
    (hN : Program.labels (d :: p) = []) (hw : Program.wp [d] (fun st => p.wp done exit st.data) exit s) :
    Program.wp (d :: p) done exit s

axiom Program.run_infix {p q : Program} [Hp : Embeds p] {o : Nat} (hq : q.IsInfixAt p o)
    (hlenq : o + q.length ≤ p.length) (hq₀ : ∀ a, ¬ q.InternalTarget a) {s₀ : MachineData}
    {done exit done' exit' : MachineState → Prop} {s : MachineData} (hw : q.wp done' exit' s)
    (hQ : ∀ st, st.pc = Host.addrOf (Hp.embedding.start + o + q.length) → done' st →
      While (·.pc ≠ Hp.embedding.endAddr)
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» exit)) done st)
    (hE : ∀ st, exit' st → p.ContinueOnInternalExit s₀
      (While (·.pc ≠ Hp.embedding.endAddr)
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» exit)) done) exit st) :
    While (·.pc ≠ Hp.embedding.endAddr)
      (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        «continue» (p.ContinueOnInternalExit s₀ «continue» exit)) done
      ⟨s, Host.addrOf (Hp.embedding.start + o)⟩

end

namespace Program.WP

scoped instance [Host] [FunDecls] : WP Program Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans p := PredTrans.mk (fun Q E s => Program.wp p (fun st => Q () st.data) (fun st => E st.pc st.data) s)
    fun hQ hE _ h => Program.wp_mono (fun st => hQ () st.data) (fun st => hE st.pc st.data) h

scoped instance [Host] [FunDecls] : WP Directive Unit (MachineData → Prop) (Int64 → MachineData → Prop) where
  trans d := WP.trans (Prog := Program) [d]

end Program.WP

/-! ## Return addresses and calls -/

opaque MachineData.retAddr (t : MachineData) : Option Int64

axiom MachineData.retAddr_eq (t : MachineData) :
    t.retAddr = (Mem.loadInt t.dmem (t.regs.get64 .rsp) 8).map
      (fun i => Int64.ofBitVec (BitVec.ofInt 64 i))
grind_pattern MachineData.retAddr_eq => t.retAddr

opaque MachineData.push64 (s : MachineData) (v : Int64) : MachineData

axiom MachineData.push64_def (s : MachineData) (v : Int64) :
    s.push64 v = { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
                          dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 v.toBitVec.toInt }

axiom MachineData.regs_push64 (s : MachineData) (v : Int64) :
    (s.push64 v).regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64)
grind_pattern MachineData.regs_push64 => (s.push64 v).regs

axiom MachineData.dmem_push64 (s : MachineData) (v : Int64) :
    (s.push64 v).dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 v.toBitVec.toInt
grind_pattern MachineData.dmem_push64 => (s.push64 v).dmem

axiom Int64.ofBitVec_ofBytes_toBytes (ra : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt))) = ra
grind_pattern Int64.ofBitVec_ofBytes_toBytes => Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)))

axiom MachineData.retAddr_push64 (s : MachineData) (ra : Int64) :
    (s.push64 ra).retAddr = some ra
grind_pattern MachineData.retAddr_push64 => (s.push64 ra).retAddr

namespace Program.WP

variable [Host] [FunDecls]

opaque _root_.FunDecls.body (f : Label) : Program

axiom _root_.FunDecls.body_eq {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g) :
    FunDecls.body f = g.prog

open Classical in
axiom wp_call_iff {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g) {asz osz : Width}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData} :
    WP.wp (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction))))) Q E s ↔
      ∀ [h : Embeds [Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction))))]],
        (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true ∧
        WP.wp (FunDecls.body f) (fun _ _ => False)
          (fun a s' => if a = h.embedding.endAddr then Q () s' else E a s') (s.push64 h.embedding.endAddr)

end Program.WP

/-! ## The specs of instructions -/

namespace Program.WP.Spec

variable [Host] [FunDecls] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

@[spec] axiom nil : ⦃ fun s => Q () s ⦄ ([] : Program) ⦃ Q; E ⦄

@[spec] axiom mov_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄

@[spec] axiom mov_mem_reg (b : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8
              (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩)
            (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄

@[spec] axiom mov_reg_sib8 (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
          ∧ Q () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄

@[spec] axiom mov_sib8_reg (b i : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true
          ∧ Q () { s with dmem := Mem.storeInt s.dmem a 8 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄

@[spec] axiom add_reg_sib8 (rd b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 8).isSome = true ∧
          let x := BitVec.ofInt 64 (Mem.loadInt s.dmem a 8).get!
          Q () { s with regs := s.regs.set64 rd (x + s.regs.get64 rd), status := StatusFlags.ofAdd x (s.regs.get64 rd) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.add (.reg (.low rd .W64)) (.regOrMem (.mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))))
    ⦃ Q; E ⦄

@[spec] axiom sub_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        Q () { s with regs := s.regs.set64 r (s.regs.get64 r - a), status := StatusFlags.ofSub (s.regs.get64 r) a } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄

@[spec] axiom add_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := BitVec.setWidth 64 i.toBitVec
        Q () { s with regs := s.regs.set64 r (a + s.regs.get64 r), status := StatusFlags.ofAdd a (s.regs.get64 r) } ⦄
      (Directive.instr (.regular asz .W64 (.add (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄

@[spec] axiom add_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        Q () { s with regs := s.regs.set64 rd (s.regs.get64 rs + s.regs.get64 rd), status := StatusFlags.ofAdd (s.regs.get64 rs) (s.regs.get64 rd) } ⦄
      (Directive.instr (.regular asz .W64
          (.add (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄

@[spec] axiom mov_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 rs) } ⦄
      (Directive.instr (.regular asz .W64 (.mov (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄

@[spec] axiom cmp_reg_reg (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        Q () { s with status := StatusFlags.ofSub (s.regs.get64 ra) (s.regs.get64 rb) } ⦄
      (Directive.instr (.regular asz .W64
          (.cmp (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
    ⦃ Q; E ⦄

@[spec] axiom test_reg_reg (asz : Width) (ra rb : Reg64) :
    ⦃ fun s =>
        ∀ af : Bool, Q () { s with
          status := StatusFlags.ofLogic (s.regs.get64 ra &&& s.regs.get64 rb) af } ⦄
      (Directive.instr (.regular asz .W64
          (.test (.reg (.low ra .W64)) (.regOrMem (.reg (.low rb .W64))))))
    ⦃ Q; E ⦄

@[spec] axiom mov_reg8_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () { s with regs := s.regs.set (.low r .W8)
                              (BitVec.ofInt 8 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).get!) } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.reg (.low r .W8)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄

@[spec] axiom mov_mem_reg8 (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 1
              (BitVec.toInt (n := 8) (s.regs.get (.low r .W8))) } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W8))))))
    ⦃ Q; E ⦄

@[spec] axiom mov_reg16_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2).isSome = true
        ∧ Q () { s with regs := s.regs.set (.low r .W16)
                              (BitVec.ofInt 16 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2).get!) } ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.reg (.low r .W16)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄

@[spec] axiom mov_mem_reg16 (b : Reg64) (d : Int64) (r : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2).isSome = true
        ∧ Q () { s with
            dmem := Mem.storeInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 2
              (BitVec.toInt (n := 16) (s.regs.get (.low r .W16))) } ⦄
      (Directive.instr (.regular .W64 .W16
          (.mov (.mem ⟨some (.reg b), none, .int64 d⟩) (.regOrMem (.reg (.low r .W16))))))
    ⦃ Q; E ⦄

@[spec] axiom dec_reg (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        Q () { s with regs := s.regs.set64 r (s.regs.get64 r - 1), status := StatusFlags.ofDec (s.regs.get64 r) s.status.cf } ⦄
      (Directive.instr (.regular asz .W64 (.dec (.reg (.low r .W64)))))
    ⦃ Q; E ⦄

@[spec] axiom inc_reg (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        Q () { s with regs := s.regs.set64 r (s.regs.get64 r + 1), status := StatusFlags.ofInc (s.regs.get64 r) s.status.cf } ⦄
      (Directive.instr (.regular asz .W64 (.inc (.reg (.low r .W64)))))
    ⦃ Q; E ⦄

@[spec] axiom xor_reg32_reg32 (asz : Width) (rd rs : Reg64) :
    ⦃ fun s =>
        let v := (s.regs.get64 rd).take 32 ^^^ (s.regs.get64 rs).take 32
        ∀ af : Bool,
          Q () { s with regs := s.regs.set64 rd (v.zeroExtend 64), status := StatusFlags.ofLogic v af } ⦄
      (Directive.instr (.regular asz .W32
          (.xor (.reg (.low rd .W32)) (.regOrMem (.reg (.low rs .W32))))))
    ⦃ Q; E ⦄

@[spec] axiom cmp_reg_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        Q () { s with status := StatusFlags.ofSub (s.regs.get64 r) (BitVec.setWidth 64 i.toBitVec) } ⦄
      (Directive.instr (.regular asz .W64 (.cmp (.reg (.low r .W64)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄

@[spec] axiom jmp_label (asz osz : Width) (l : Label) :
    ⦃ fun s => E (label l) s ⦄
      (Directive.instr (.regular asz osz (.jmp (.rel (.sub (.label l) .after_current_instruction)))))
    ⦃ Q; E ⦄

@[spec] axiom jcc_label (asz osz : Width) (cc : CondCode) (l : Label) :
    ⦃ fun s => (cc.interp s.status = true → E (label l) s) ∧ (cc.interp s.status = false → Q () s) ⦄
      (Directive.instr (.regular asz osz (.jcc cc l)))
    ⦃ Q; E ⦄

@[spec] axiom push_reg (rs : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
                        dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 (s.regs.get64 rs).toInt } ⦄
      (Directive.instr (.regular .W64 .W64 (.push (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄

@[spec] axiom pop_reg (rd : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).isSome = true
        ∧ Q () { s with
            regs := (s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64)).set64 rd
              (BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 .rsp) 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64 (.pop (.reg (.low rd .W64)))))
    ⦃ Q; E ⦄

@[spec] axiom ret (asz osz : Width) :
    ⦃ fun s => s.retAddr.isSome = true
        ∧ E s.retAddr.get! { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp + 8#64) } ⦄
      (Directive.instr (.regular asz osz .ret))
    ⦃ Q; E ⦄

@[spec] axiom call_label {f : Label} (asz osz : Width)
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} :
    ⦃ fun s => Mem.Mapped [(s.regs.rsp.toBitVec - 8#64, 8)] s.dmem
        ∧ ∀ ra, WP.wp (FunDecls.body f) (fun _ _ => False)
          (fun a s' => (a = ra → Q () s') ∧ (a ≠ ra → E a s')) (s.push64 ra) ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ Q; E ⦄

axiom movzx_reg32_sib1 (r b i : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
          ∧ Q () { s with regs := s.regs.set (.low r .W32)
                              (BitVec.zeroExtend 32 (BitVec.ofInt 8 (Mem.loadInt s.dmem a 1).get!)) } ⦄
      (Directive.instr (.regular .W64 .W32
          (@Operation.movzx .W32 .W8 (.reg (.low r .W32)) (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩))))
    ⦃ Q; E ⦄

axiom movzx_reg32_mem1 (r b : Reg64) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
          ∧ Q () { s with regs := s.regs.set (.low r .W32)
                              (BitVec.zeroExtend 32 (BitVec.ofInt 8 (Mem.loadInt s.dmem a 1).get!)) } ⦄
      (Directive.instr (.regular .W64 .W32
          (@Operation.movzx .W32 .W8 (.reg (.low r .W32)) (.mem ⟨some (.reg b), none, .int64 d⟩))))
    ⦃ Q; E ⦄

axiom mov_sib1_reg8 (b i : Reg64) (d : Int64) (rs : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + s.regs.get64 i + BitVec.ofInt 64 d.toInt
        (Mem.loadInt s.dmem a 1).isSome = true
          ∧ Q () { s with dmem := Mem.storeInt s.dmem a 1 (BitVec.toInt (n := 8) (s.regs.get (.low rs .W8))) } ⦄
      (Directive.instr (.regular .W64 .W8
          (.mov (.mem ⟨some (.reg b), some ⟨i, .W8⟩, .int64 d⟩) (.regOrMem (.reg (.low rs .W8))))))
    ⦃ Q; E ⦄

axiom mov_reg_mem (r b : Reg64) (d : Int64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).isSome = true
        ∧ Q () { s with regs := s.regs.set64 r (BitVec.ofInt 64 (Mem.loadInt s.dmem (s.regs.get64 b + BitVec.ofInt 64 d.toInt) 8).get!) } ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64)) (.regOrMem (.mem ⟨some (.reg b), none, .int64 d⟩)))))
    ⦃ Q; E ⦄

axiom sub_reg_reg (asz : Width) (rd rs : Reg64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 rd - s.regs.get64 rs), status := StatusFlags.ofSub (s.regs.get64 rd) (s.regs.get64 rs) } ⦄
      (Directive.instr (.regular asz .W64 (.sub (.reg (.low rd .W64)) (.regOrMem (.reg (.low rs .W64))))))
    ⦃ Q; E ⦄

axiom shr_reg_one (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ af : Bool, Q () { s with regs := s.regs.set64 r ((s.regs.get64 r).ushiftRight 1), status := StatusFlags.from_result ((s.regs.get64 r).ushiftRight 1) { cf := (s.regs.get64 r).getLsbD 0, af := af, of := (s.regs.get64 r).msb } } ⦄
      (Directive.instr (.regular asz .W64 (.shr (.reg (.low r .W64)) (.imm8 (.int64 1)))))
    ⦃ Q; E ⦄

axiom mov_reg8_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r ((s.regs.get64 r).replaceLow (i.toBitVec.truncate 8)) } ⦄
      (Directive.instr (.regular asz .W8 (.mov (.reg (.low r .W8)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄

axiom test_reg8_reg8 (asz : Width) (ra rb : Reg64) :
    ⦃ fun s => ∀ af : Bool, Q () { s with status := StatusFlags.from_result ((s.regs.get64 ra).take 8 &&& (s.regs.get64 rb).take 8) { cf := false, af := af, of := false } } ⦄
      (Directive.instr (.regular asz .W8 (.test (.reg (.low ra .W8)) (.regOrMem (.reg (.low rb .W8))))))
    ⦃ Q; E ⦄

axiom push_reg16 (rs : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 2#64) 2).isSome = true
        ∧ Q () { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 2#64),
                        dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 2#64) 2
                          (BitVec.toInt (n := 16) (s.regs.get (.low rs .W16))) } ⦄
      (Directive.instr (.regular .W64 .W16 (.push (.regOrMem (.reg (.low rs .W16))))))
    ⦃ Q; E ⦄

axiom pop_reg16 (rd : Reg64) :
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp) 2).isSome = true
        ∧ Q () { s with
            regs := (s.regs.set64 .rsp (s.regs.get64 .rsp + 2#64)).set (.low rd .W16)
              (BitVec.ofInt 16 (Mem.loadInt s.dmem (s.regs.get64 .rsp) 2).get!) } ⦄
      (Directive.instr (.regular .W64 .W16 (.pop (.reg (.low rd .W16)))))
    ⦃ Q; E ⦄

axiom lea_reg_sib (rd b i : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 b + s.regs.get64 i * 8 + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low rd .W64) ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩)))
    ⦃ Q; E ⦄

axiom lea_reg_base_disp (rd b : Reg64) (d : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 rd (s.regs.get64 b + BitVec.ofInt 64 d.toInt) } ⦄
      (Directive.instr (.regular .W64 .W64 (.lea (.low rd .W64) ⟨some (.reg b), none, .int64 d⟩)))
    ⦃ Q; E ⦄

axiom mov_reg32_imm (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s => Q () { s with regs := s.regs.set64 r ((i.toBitVec.setWidth 32).zeroExtend 64) } ⦄
      (Directive.instr (.regular asz .W32 (.mov (.reg (.low r .W32)) (.imm (.int64 i)))))
    ⦃ Q; E ⦄

end Program.WP.Spec

/-! ## The control-flow graph of a text -/

opaque Program.Intercept [Host] (ls : List Label) (s₀ : MachineData)
    (I' : Label → Nat → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (a : Int64) (s : MachineData) : Prop

section
variable [Host] {ls : List Label} {s₀ s : MachineData} {I' : Label → Nat → MachineData → Prop}
  {E : Int64 → MachineData → Prop} {a : Int64}

axiom Program.Intercept.intro
    (h : (s.StackAtOrBelow s₀ ∧ ∃ l, label l = a ∧ l ∈ ls ∧ I' l (ls.idxOf l + 1) s)
      ∨ (E a s ∧ ∀ l ∈ ls, label l = a → s₀.StackBelow s)) :
    Program.Intercept ls s₀ I' E a s

axiom Program.Intercept.dispatch {p : Program} {C X : MachineState → Prop} {d : MachineData} {a : Int64}
    (h : Program.Intercept (Program.labels p) s₀ I' E a d)
    (hc : ∀ i l, (Program.labels p)[i]? = some l → label l = a → d.StackAtOrBelow s₀ →
      I' l (i + 1) d → C ⟨d, a⟩)
    (hx : E a d → X ⟨d, a⟩) :
    p.ContinueOnInternalExit s₀ C X ⟨d, a⟩

axiom Program.labels_nodup_of_embeds {p : Program} [H : Embeds p] : (Program.labels p).Nodup

axiom Program.blockAt_noInternal {p : Program} {l : Label} {blk : Program.Block}
    (h : Program.blockAt p l = some blk) (a : Int64) : ¬ blk.body.InternalTarget a

axiom Program.entry_noInternal (p : Program) (a : Int64) : ¬ (Program.view p).1.InternalTarget a

end

/-! ## The simp set of `vcgen` -/

@[vcgen_simp] theorem BitVec.ofInt_toInt_int64_zero {w : Nat} :
    BitVec.ofInt w (Int64.toInt 0) = (0 : BitVec w) := by
  simp

attribute [vcgen_simp] UInt64.toBitVec_ofBitVec BitVec.ofNat_eq_ofNat BitVec.setWidth_eq BitVec.add_zero
  BitVec.toNat_ofNat Int.cast_ofNat_Int BitVec.xor_self Option.map_some Option.get!_some
  Option.isSome_some BitVec.ofInt_toInt List.cons_append List.nil_append Program.labels_nil
  Program.labels_cons_instr List.cons_ne_nil BitVec.zero_eq beq_iff_eq

@[vcgen_rintro] theorem List.forall_mem_cons_intro {α : Type _} {G : α → Prop} {a : α} {l : List α}
    (ha : G a) (hl : ∀ x, x ∈ l → G x) : ∀ x, x ∈ a :: l → G x :=
  List.forall_mem_cons.mpr ⟨ha, hl⟩

@[vcgen_rintro] theorem List.forall_mem_nil_intro {α : Type _} {G : α → Prop} :
    ∀ x, x ∈ ([] : List α) → G x :=
  fun _ h => nomatch h

attribute [grind cases] Instr.IsPadding
