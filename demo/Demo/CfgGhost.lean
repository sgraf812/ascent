import Kraken.StateCfg

/-!
# The control-flow rule with a ghost state

`Program.WP.cfg_ghost` is the control-flow rule of `Program.WP.cfg` for an invariant `I l s g` that
also relates the machine state `s` at the label `l` to a ghost state `g`, and for a variant that is a
well-founded relation `R` on pairs of a label and a ghost state. Every jump and every fall-through
out of a labelled block goes to a pair below the pair of the block. For example, with the abstract
state of a refinement as the ghost state, `R` is the successor relation of the abstract
control-flow graph on the states from which the abstract program terminates.
-/

open Std.WP Lean.Order

abbrev Program.GhostLift {G : Type} (I : Label → MachineData → G → Prop) (s₀ : MachineData) (g₀ : G) :
    Option Label → MachineData → G → Prop
  | none, s, g => s = s₀ ∧ g = g₀
  | some l, s, g => I l s g

abbrev Program.GhostDec {G : Type} (R : Label × G → Label × G → Prop) :
    Option Label → G → Label → G → Prop
  | none, _, _, _ => True
  | some l, g, l', g' => R (l', g') (l, g)

abbrev Program.GhostNext {G : Type} (I : Label → MachineData → G → Prop) (Q : Unit → MachineData → Prop)
    (R : Label × G → Label × G → Prop) (lbl : Option Label) (g : G) : Option Label → MachineData → Prop
  | some l', s => ∃ g', I l' s g' ∧ Program.GhostDec R lbl g l' g'
  | none, s => Q () s

namespace Program.WP

variable [Host] [FunDecls]

theorem cfg_ghost {G : Type} {p : Program} {s₀ : MachineData} {g₀ : G} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (I : Label → MachineData → G → Prop)
    (R : Label × G → Label × G → Prop) (hR : WellFounded R)
    (h : ∀ blk ∈ Program.blocks p, ∀ t g, Program.GhostLift I s₀ g₀ blk.label t g →
      WP.wp blk.body (fun _ => Program.GhostNext I Q R blk.label g blk.next)
        (Program.Intercept (Program.labels p) s₀
          (fun l _ s => ∃ g', I l s g' ∧ Program.GhostDec R blk.label g l g') E) t) :
    WP.wp p Q E s₀ := by
  show Program.wp p (fun st => Q () st.data) (fun st => E st.pc st.data) s₀
  rw [Program.wp_eq]
  intro H
  have hlink := H.embedding.isInfixAt
  have hnd : (Program.labels p).Nodup := Program.labels_nodup_of_embeds
  have hcellOf : ∀ l, Program.fromLabel p l ≠ [] →
      p[p.length - (Program.fromLabel p l).length]? = some (Directive.label l) := by
    intro l hne
    have hdrop := Program.drop_fromLabel p l
    obtain ⟨t, rest, -, hfl, -, -⟩ := Program.fromLabel_split hnd hne
    conv at hdrop => rhs; rw [hfl]
    simpa [List.head?_drop] using congrArg List.head? hdrop
  have hne_of : ∀ l', (Program.blockAt p l').isSome → Program.fromLabel p l' ≠ [] := by
    intro l' hsome'
    obtain ⟨blk', hblk'⟩ := Option.isSome_iff_exists.mp hsome'
    rw [Program.fromLabel_block hnd hblk']
    exact List.cons_ne_nil _ _
  have key : ∀ x : Label × G, ∀ s, (Program.blockAt p x.1).isSome → I x.1 s x.2 →
      While (·.pc ≠ H.embedding.endAddr)
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» fun st => E st.pc st.data))
        (fun st => Q () st.data)
        ⟨s, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p x.1).length))⟩ := by
    intro x
    induction x using hR.induction with
    | _ x ih =>
      obtain ⟨l, g⟩ := x
      intro s hsome hI
      dsimp only at hsome hI ⊢
      have jump : ∀ l' s' g', (Program.blockAt p l').isSome → I l' s' g' → R (l', g') (l, g) →
          While (·.pc ≠ H.embedding.endAddr)
            (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
              «continue» (p.ContinueOnInternalExit s₀ «continue» fun st => E st.pc st.data))
            (fun st => Q () st.data) ⟨s', label l'⟩ := by
        intro l' s' g' hsome' hI' hlt
        rw [Host.label_eq hlink (hcellOf l' (hne_of l' hsome'))]
        exact ih (l', g') hlt s' hsome' hI'
      obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hlab, i', hi', hnext', hidx⟩ := Program.blockAtAux_spec hblk
      have hb := h blk (Program.mem_blocks_of_blockAt hblk)
      rw [hlab] at hb
      have htext := Program.fromLabel_block hnd hblk
      have hlen := congrArg List.length htext
      simp only [List.length_cons, List.length_append] at hlen
      have hdrop := Program.drop_fromLabel p l
      have hsuf : (Program.fromLabel p l).length ≤ p.length := by
        have := congrArg List.length hdrop
        simp only [List.length_drop] at this
        omega
      generalize hi : p.length - (Program.fromLabel p l).length = i at hdrop ⊢
      rw [htext] at hdrop
      have hbody : blk.body.IsInfixAt p (i + 1) :=
        ⟨Program.fromNext p blk.next, by rw [← List.drop_drop, hdrop]; rfl⟩
      have hpi : p[i]? = some (.label l) := by
        have h0 := congrArg (·[0]?) hdrop
        simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using h0
      have hlab' : Host.prog[H.embedding.start + i]? = some (.label l) := by
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hpi
        rw [List.isInfixAt_iff_getElem?.mp hlink i hlt, heq]
      have haddr : Host.addrOf (H.embedding.start + (i + 1)) = Host.addrOf (H.embedding.start + i) := by
        rw [← Nat.add_assoc, Host.addrOf_succ hlab', Host.label_size _ _ hlab']; simp
      rw [← haddr]
      refine Program.run_infix (o := i + 1) hbody (by omega) (Program.blockAt_noInternal hblk)
        (hb s g hI) ?_ ?_
      · intro st hpc hnext
        cases hn : blk.next with
        | none =>
          simp only [hn] at hnext hlen
          refine While.stop ?_ hnext
          show ¬ st.pc ≠ Host.addrOf (H.embedding.start + p.length)
          rw [hpc]
          simp only [Program.fromNext, List.length_nil] at hlen
          intro hne
          exact hne (by congr 1; omega)
        | some l' =>
          simp only [hn] at hnext hlen
          obtain ⟨g', hI', hdec⟩ := hnext
          obtain ⟨hsome', -⟩ := Program.blockAt_next hnd hblk hn
          simp only [Program.fromNext] at hlen
          have hst : st = ⟨st.data, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p l').length))⟩ := by
            cases st
            simp only [MachineState.mk.injEq, true_and] at hpc ⊢
            rw [hpc]
            congr 1
            omega
          rw [hst]
          exact ih (l', g') hdec st.data hsome' hI'
      · rintro ⟨d, a⟩ hst
        refine Program.Intercept.dispatch hst (fun j l' hl' hla _ hI' => ?_) id
        subst hla
        obtain ⟨g', hI'', hdec⟩ := hI'
        exact jump l' d g' (Program.isSome_blockAt_of_mem (List.mem_of_getElem? hl')) hI'' hdec
  have hq : (Program.view p).1.IsInfixAt p 0 := ⟨_, (Program.view_eq_entry hnd).symm⟩
  have hlen0 := congrArg List.length (Program.view_eq_entry hnd)
  simp only [List.length_append] at hlen0
  refine Program.run_infix (o := 0) hq (by omega) (Program.entry_noInternal p)
    (h _ (Program.entryBlock_mem_blocks p) s₀ g₀ ⟨rfl, rfl⟩) ?_ ?_
  · intro st hpc hnext
    simp only [Program.entryBlock] at hnext hlen0
    cases hv : (Program.view p).2 with
    | nil =>
      simp only [hv, Program.firstLabel, Program.fromNext, List.length_nil] at hnext hlen0
      refine While.stop ?_ hnext
      show ¬ st.pc ≠ Host.addrOf (H.embedding.start + p.length)
      rw [hpc]
      intro hne
      exact hne (by congr 1; omega)
    | cons lb rest =>
      obtain ⟨l', b'⟩ := lb
      simp only [hv, Program.firstLabel, Program.fromNext] at hnext hlen0
      obtain ⟨g', hI', -⟩ := hnext
      have hsome' : (Program.blockAt p l').isSome := by
        have hndv : ((Program.view p).2.map (·.1)).Nodup := by rwa [← Program.labels_view]
        have h0 : (Program.view p).2[0]? = some (l', b') := by rw [hv]; rfl
        show (Program.blockAtAux 1 (Program.view p).2 l').isSome = true
        rw [Program.blockAtAux_of_getElem hndv h0]
        rfl
      have hst : st = ⟨st.data, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p l').length))⟩ := by
        cases st
        simp only [MachineState.mk.injEq, true_and] at hpc ⊢
        rw [hpc]
        congr 1
        omega
      rw [hst]
      exact key (l', g') st.data hsome' hI'
  · rintro ⟨d, a⟩ hst
    refine Program.Intercept.dispatch hst (fun j l' hl' hla _ hI' => ?_) id
    subst hla
    obtain ⟨g', hI'', -⟩ := hI'
    have hsome' := Program.isSome_blockAt_of_mem (List.mem_of_getElem? hl')
    rw [Host.label_eq hlink (hcellOf l' (hne_of l' hsome'))]
    exact key (l', g') d hsome' hI''

end Program.WP
