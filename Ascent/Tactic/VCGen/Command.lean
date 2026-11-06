import Ascent.Tactic.VCGen.Frontend

/-!
# The `ascend_def` and `simp_def` commands

`ascend_def a xs : T from ⦃P⦄ c ⪯[γ] a ⦃Q; E⦄ ascend [specs] with tac` defines `a : ∀ xs, T` as the
abstract program that `ascend` synthesizes for `c`, and proves the refinement as the theorem
`a.refines`. In the statement, `a` is a variable of type `T` that stands for `a xs`. The command
replaces `a` by a synthesis hole, runs `ascend` with the head definition of `c` unfolded and the
specs of the `ascend` clause, and closes every VC with the `grind` step `tac`.

`simp_def a xs : T from c using [lemmas]` is the simplification between two runs: it defines
`a : ∀ xs, T` as `c` simplified by `simp only [lemmas]`, and proves `a.eq : ∀ xs, c = a xs`.
`Ascent.bind_seq_assoc` groups a chain of steps so that its last step is on top, the form in which
a rule about the end of a block applies.
-/

namespace Ascent

/-- A chain of steps with its last step on top. -/
theorem bind_seq_assoc {m : Type u → Type v} [Monad m] [LawfulMonad m] {α β γ : Type u}
    (x : m α) (y : m β) (z : m γ) :
    (x >>= fun _ => y >>= fun _ => z) = ((x >>= fun _ => y) >>= fun _ => z) := by
  rw [bind_assoc]

end Ascent

open Lean Meta Elab Command Term

namespace Lean.Elab.Tactic.VCGen.Ascend

syntax (name := ascendDefCmd)
  "ascend_def " ident bracketedBinder* " : " term " from " term
    (&" ascend " "[" term,* "]")? (" with " vcgenDischarge)? : command

/-- The head constant of the concrete program `c`, if `ascend` can unfold it: a definition that
is neither a projection nor an instance. -/
def unfoldableHead? (c : Expr) : MetaM (Option Name) := do
  let some declName := c.getAppFn.constName? | return none
  let env ← getEnv
  let some (.defnInfo _) := env.find? declName | return none
  if env.isProjectionFn declName || (← isInstance declName) then return none
  return some declName

/-- `ascend_def f xs : T from stmt ascend [specs] with tac` synthesizes `f : ∀ xs, T` from the
refinement statement `stmt`, in which `f` stands for `f xs`, and proves `f.refines : ∀ xs, stmt`.
The run unfolds the head of the concrete program and takes the specs of the `ascend` clause; the
`grind` step `tac` closes every verification condition. -/
elab_rules : command
  | `(ascend_def $name $binders* : $type from $stmt $[ascend [$specs,*]]? $[with $tac?]?) =>
    liftTermElabM <| Term.elabBinders binders fun xs => do
    let T ← elabType type
    synthesizeSyntheticMVarsNoPostponing
    let stmtFn ← withLocalDeclD name.getId T fun x => do
      let e ← elabType stmt
      synthesizeSyntheticMVarsNoPostponing
      mkLambdaFVars #[x] (← instantiateMVars e)
    let hole ← mkFreshExprMVar T
    let goalType := stmtFn.beta #[hole]
    unless goalType.isAppOfArity ``Ascent.Refinement 22 do
      throwError "ascend_def: the statement is not a refinement:{indentExpr goalType}"
    let proof ← mkFreshExprSyntheticOpaqueMVar goalType
    let specs := (specs.map (·.getElems)).getD #[]
    let specs ← match ← unfoldableHead? goalType.getAppArgs[13]! with
      | some declName => pure (specs.push (mkIdent declName))
      | none => pure specs
    let ascendStx ← match tac? with
      | some tac => `(tactic| ascend [$specs,*] with $tac)
      | none => `(tactic| ascend [$specs,*])
    let (vcs, _) ← Lean.Elab.runTactic proof.mvarId! ascendStx
    if let vc :: _ := vcs then
      throwError "ascend_def: unsolved verification condition:{indentExpr (← vc.getType)}\n\
        provide a `with` clause"
    let value ← instantiateMVars hole
    if value.hasMVar then
      throwError "ascend_def: the synthesized program has holes:{indentExpr value}"
    addDecl <| .defnDecl {
      name := name.getId, levelParams := [], type := ← mkForallFVars xs T,
      value := ← mkLambdaFVars xs value, hints := .regular 0, safety := .safe }
    enableRealizationsForConst name.getId
    let proof ← instantiateMVars proof
    if proof.hasMVar then
      throwError "ascend_def: the refinement proof has holes"
    addDecl <| .thmDecl {
      name := name.getId ++ `refines, levelParams := [],
      type := ← mkForallFVars xs (stmtFn.beta #[mkAppN (mkConst name.getId) xs]),
      value := ← mkLambdaFVars xs proof }

syntax (name := simpDefCmd)
  "simp_def " ident bracketedBinder* " : " term " from " term
    " using " "[" Lean.Parser.Tactic.simpLemma,* "]" : command

/-- `simp_def f xs : T from c using [lemmas]` defines `f : ∀ xs, T` as `c` simplified by
`simp only [lemmas]` and proves `f.eq : ∀ xs, c = f xs`. -/
elab_rules : command
  | `(simp_def $name $binders* : $type from $c using [$lemmas,*]) =>
    liftTermElabM <| Term.elabBinders binders fun xs => do
    let T ← elabType type
    let c ← Term.elabTermEnsuringType c T
    synthesizeSyntheticMVarsNoPostponing
    let c ← instantiateMVars c
    let rhs ← mkFreshExprMVar T
    let proof ← mkFreshExprSyntheticOpaqueMVar (← mkEq c rhs)
    let lemmas : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
      ``Lean.Parser.Tactic.simpLemma] "," := ⟨lemmas.elemsAndSeps⟩
    let simpStx ← `(tactic| (conv => lhs; simp only [$lemmas,*]) <;> exact rfl)
    let (gs, _) ← Lean.Elab.runTactic proof.mvarId! simpStx
    unless gs.isEmpty do throwError "simp_def: the simplification left goals"
    let value ← instantiateMVars rhs
    if value.hasMVar then throwError "simp_def: the simplified program has holes:{indentExpr value}"
    addDecl <| .defnDecl {
      name := name.getId, levelParams := [], type := ← mkForallFVars xs T,
      value := ← mkLambdaFVars xs value, hints := .regular 0, safety := .safe }
    enableRealizationsForConst name.getId
    let proof ← instantiateMVars proof
    addDecl <| .thmDecl {
      name := name.getId ++ `eq, levelParams := [],
      type := ← mkForallFVars xs (← mkEq c (mkAppN (mkConst name.getId) xs)),
      value := ← mkLambdaFVars xs proof }

syntax (name := symSimpDefCmd)
  "sym_simp_def " ident bracketedBinder* " : " term " from " term
    " using " &"pre " "[" ident,* "]" &" post " "[" ident,* "]" : command

def symSimpTheorems (ids : Array Ident) : MetaM Sym.Simp.Theorems := do
  let mut thms : Sym.Simp.Theorems := {}
  for id in ids do
    for thm in ← Sym.Simp.mkTheoremsFromDecl (← realizeGlobalConstNoOverload id) do
      thms := thms.insert thm
  return thms

/-- `sym_simp_def f xs : T from c using pre [ps] post [qs]` defines `f : ∀ xs, T` as `c` simplified by
`Sym.simp`, rewriting with `ps` before and with `qs` and the `vcgen_simp` set after visiting the
subterms of a term, and proves `f.eq : ∀ xs, c = f xs`. -/
elab_rules : command
  | `(sym_simp_def $name $binders* : $type from $c using pre [$pres,*] post [$posts,*]) =>
    liftTermElabM <| Term.elabBinders binders fun xs => do
    let T ← elabType type
    let c ← Term.elabTermEnsuringType c T
    synthesizeSyntheticMVarsNoPostponing
    let c ← instantiateMVars c
    let preThms ← symSimpTheorems pres.getElems
    let postThms ← symSimpTheorems posts.getElems
    let vcThms ← vcgenSimpExt.getTheorems
    let (value, proof) ← Sym.SymM.run do
      let c ← Sym.shareCommon c
      let methods : Sym.Simp.Methods :=
        { pre := Sym.Simp.beta >> Sym.Simp.reduceProj >> Sym.Simp.reduceMatcher >>
            Sym.Simp.reduceControl >> preThms.rewrite Sym.Simp.dischargeSimpSelf
          post := Sym.Simp.evalGround >> vcThms.rewrite >>
            postThms.rewrite Sym.Simp.dischargeSimpSelf }
      let (r, _) ← Sym.Simp.SimpM.run (Sym.Simp.simp c) methods
      match r with
      | .rfl .. => return (c, ← mkEqRefl c)
      | .step e h .. => return (e, h)
    let value ← instantiateMVars value
    if value.hasMVar then throwError "sym_simp_def: the simplified program has holes:{indentExpr value}"
    addDecl <| .defnDecl {
      name := name.getId, levelParams := [], type := ← mkForallFVars xs T,
      value := ← mkLambdaFVars xs value, hints := .regular 0, safety := .safe }
    enableRealizationsForConst name.getId
    let proof ← instantiateMVars proof
    addDecl <| .thmDecl {
      name := name.getId ++ `eq, levelParams := [],
      type := ← mkForallFVars xs (← mkEq c (mkAppN (mkConst name.getId) xs)),
      value := ← mkLambdaFVars xs proof }

end Lean.Elab.Tactic.VCGen.Ascend
