import Kraken.X64.Parser
import Kraken.X64.PrintATT
import Kraken.X64.PrettyPrint

/-!
# Printing programs as `parse(…)`

A closed `Program` term delaborates to the `parse("…")` invocation that elaborates to it, with the
text in AT&T syntax, labels at the margin and instructions indented by two spaces.
-/

open Lean Meta PrettyPrinter Delaborator SubExpr Kraken.X64.Parser

private def parseLayout (p : Program) : String :=
  "\n" ++ String.join (p.map fun d =>
    match d with
    | .label _ => Kraken.X64.ATT.directive d ++ "\n"
    | _ => "  " ++ Kraken.X64.ATT.directive d ++ "\n")

private unsafe def programTextImpl (e : Expr) : MetaM (Option String) := do
  if e.hasFVar || e.hasMVar then return none
  try
    return some (parseLayout (← evalExpr Program (mkApp (mkConst ``List [0]) (mkConst ``Directive)) e))
  catch _ =>
    return none

@[implemented_by programTextImpl]
private def programText? (_e : Expr) : MetaM (Option String) := return none

@[app_delab List.cons]
def delabProgramParse : Delab := do
  if ← getPPOption getPPExplicit then failure
  let e ← getExpr
  unless e.getAppNumArgs == 3 && (e.getArg! 0).isConstOf ``Directive do failure
  let some s ← programText? e | failure
  let lit := s.foldl (fun acc c => if c == '"' || c == '\\' then acc.push '\\' |>.push c else acc.push c) "\""
  `(parse($(⟨Syntax.mkLit strLitKind (lit.push '"')⟩)))
