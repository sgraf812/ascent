import Ascent.FixLoop
import Lean.PrettyPrinter.Delaborator.Builtins

/-!
# Printing `FixLoop` loops in `do` notation

`FixLoop.mk.forIn init fun _ v => body`, and `ForIn.forIn` over `FixLoop.mk`, print as the
`repeat'` or `while'` statement that elaborates to it:

```
do
  let mut i := 0
  while' ¬n = i do
    modify fun o => o.set! i (a[i]! + b[i]!)
    i := i + 1
  pure i
```

The body prints as a `do` sequence: `pure (.yield e)` is `i := e; continue`, `pure (.done e)` is
`i := e; break`, a bind is `let x ← …`, and `ite` is `if … then … else …`. A `continue` at the end of
the body is left out. A loop over `PUnit` has no `let mut`. A bind of a loop prints as the loop
statement inside the enclosing block, and the rest of the block reads the loop variable. A loop whose body
mentions `ForInStep` anywhere else prints as a term, and so does every loop under `pp.explicit`.
-/

namespace Ascent.FixLoop

open Lean Lean.Meta Lean.Parser.Term Lean.PrettyPrinter Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

private def isUnitType (e : Expr) : Bool :=
  e.isConstOf ``Unit || e.isConstOf ``PUnit

private def mentionsForInStep (e : Expr) : Bool :=
  (e.find? fun e => e.isConstOf ``ForInStep.yield || e.isConstOf ``ForInStep.done).isSome

private def stepValue? (e : Expr) : Option (Name × Expr) :=
  if e.isAppOfArity ``Pure.pure 4 then
    let s := e.appArg!
    if s.isAppOfArity ``ForInStep.yield 2 then some (``ForInStep.yield, s.appArg!)
    else if s.isAppOfArity ``ForInStep.done 2 then some (``ForInStep.done, s.appArg!)
    else none
  else none

private def mkSeq (items : Array (TSyntax `doElem)) : DelabM (TSyntax ``Parser.Term.doSeq) := do
  let items := if items.size > 1 && items.back!.raw.isOfKind ``Parser.Term.doContinue then items.pop
    else items
  let items ← items.mapM fun i => `(doSeqItem| $i:doElem)
  `(doSeq| $items:doSeqItem*)

private def loopVarElems (v : Option (Ident × Expr)) (arg : Expr) (pos : DelabM Term) :
    DelabM (Array (TSyntax `doElem)) := do
  match v with
  | some (n, fv) =>
    if arg == fv then return #[]
    let rhs ← pos
    return #[← `(doElem| $n:ident := $rhs)]
  | none => return #[]

private partial def delabBody (v : Option (Ident × Expr)) :
    DelabM (Array (TSyntax `doElem)) := do
  let e ← getExpr
  if let some (k, arg) := stepValue? e then
    let assign ← withAppArg <| withAppArg <| loopVarElems v arg delab
    if k == ``ForInStep.yield then
      return assign.push (← `(doElem| continue))
    return assign.push (← `(doElem| break))
  if e.isAppOfArity ``Bind.bind 6 then
    let α := e.getArg! 2
    let ma ← withNaryArg 4 delab
    if mentionsForInStep (e.getArg! 4) then failure
    let .lam _ _ body _ := e.getArg! 5 | failure
    return ← withNaryArg 5 <| withBindingBodyUnusedName fun n => do
      let first ←
        if body.hasLooseBVars then `(doElem| let $(⟨n⟩):ident ← $ma:term)
        else if isUnitType α then `(doElem| $ma:term)
        else `(doElem| let _ ← $ma:term)
      return #[first] ++ (← delabBody v)
  if let .letE n t val _ nondep := e then
    let n ← getUnusedName n e.letBody!
    let stxT ← descend t 0 delab
    let stxV ← descend val 1 delab
    let first ←
      if nondep then `(doElem| have $(mkIdent n) : $stxT := $stxV)
      else `(doElem| let $(mkIdent n) : $stxT := $stxV)
    return ← withLetDecl n t val (nondep := nondep) fun fvar =>
      descend (e.letBody!.instantiate1 fvar) 2 do
        return #[first] ++ (← delabBody v)
  if e.isAppOfArity ``ite 5 then
    let c ← withNaryArg 1 delab
    let t ← mkSeq (← withNaryArg 3 (delabBody v))
    let f ← mkSeq (← withNaryArg 4 (delabBody v))
    return #[← `(doElem| if $c:term then $t else $f)]
  if mentionsForInStep e then failure
  return #[← `(doElem| $(← delab):term)]

private def loopArgs? (e : Expr) : Option (Nat × Nat × Nat) :=
  if e.isAppOfArity ``FixLoop.forIn 7 then some (3, 5, 6)
  else if e.isAppOfArity ``ForIn.forIn 8 && (e.getArg! 1).isConstOf ``FixLoop then some (4, 6, 7)
  else none

private def isDoneOf (fv : Expr) (e : Expr) : Bool :=
  match stepValue? e with
  | some (k, arg) => k == ``ForInStep.done && arg == fv
  | none => false

private def delabLoopElems : DelabM (Array (TSyntax `doElem) × Option Ident) := do
  let e ← getExpr
  let some (iβ, iInit, iF) := loopArgs? e | failure
  let unitLoop := isUnitType (e.getArg! iβ)
  let init ← withNaryArg iInit delab
  let .lam _ _ (.lam _ _ _ _) _ := e.getArg! iF | failure
  withNaryArg iF <| withBindingBodyUnusedName fun _ => withBindingBodyUnusedName fun n => do
    let fv := (← getLCtx).lastDecl.get!.toExpr
    let v := if unitLoop then none else some (⟨n⟩, fv)
    let body ← getExpr
    let loop ←
      if body.isAppOfArity ``ite 5 && isDoneOf fv (body.getArg! 4) then
        let c ← withNaryArg 1 delab
        let s ← mkSeq (← withNaryArg 3 (delabBody v))
        `(doElem| while' $c do $s)
      else
        let s ← mkSeq (← delabBody v)
        `(doElem| repeat' $s)
    if unitLoop then return (#[loop], none)
    return (#[← `(doElem| let mut $(⟨n⟩):ident := $init), loop], some ⟨n⟩)

@[delab app.Ascent.FixLoop.forIn, delab app.ForIn.forIn]
def delabForIn : Delab := whenNotPPOption getPPExplicit do
  let (elems, v) ← delabLoopElems
  let elems ← match v with
    | some n => pure (elems.push (← `(doElem| $(mkIdent `pure):ident $n:ident)))
    | none => pure elems
  let items ← elems.mapM fun i => `(doSeqItem| $i:doElem)
  `(do $items:doSeqItem*)

@[delab app.Bind.bind]
def delabBindForIn : Delab := whenNotPPOption getPPExplicit do
  let e ← getExpr
  guard <| e.isAppOfArity ``Bind.bind 6 && (loopArgs? (e.getArg! 4)).isSome
  let .lam _ _ body _ := e.getArg! 5 | failure
  let (loop, v) ← withNaryArg 4 delabLoopElems
  let rest ← withNaryArg 5 <|
    match v with
    | some n => withBindingBody n.getId delabDoElems
    | none => do
      guard !body.hasLooseBVars
      withBindingBodyUnusedName fun _ => delabDoElems
  let items ← (loop ++ rest.toArray.map (fun s => (⟨s⟩ : TSyntax `doElem))).mapM fun i => `(doSeqItem| $i:doElem)
  `(do $items:doSeqItem*)

end Ascent.FixLoop
