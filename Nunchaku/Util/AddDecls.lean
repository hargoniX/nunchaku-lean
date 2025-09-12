module
import Lean.Util.SCC
public import Lean.AddDecl
public import Nunchaku.Util.TransforM

namespace Nunchaku

open Lean Core

#check SCC.scc
#check addDecl

def declarationName (decl : Declaration) : Name :=
  match decl with
  | .axiomDecl val | .defnDecl val |  .opaqueDecl val => val.name
  | .inductDecl _ _ [ty] _ => ty.name
  | .inductDecl .. | .mutualDefnDecl .. | .quotDecl .. | .thmDecl .. => unreachable!

def declarationDependencies (decl : Declaration) : TransforM (List Name) := do
  match decl with
  | .axiomDecl val | .opaqueDecl val => return Expr.getUsedConstants val.type |>.toList
  | .inductDecl _ _ [ty] _ =>
    let tyConsts := Expr.getUsedConstantsAsSet ty.type
    let allConsts := ty.ctors.foldl (init := tyConsts) fun acc ctor =>
      acc.insertMany ctor.type.getUsedConstants
    return allConsts.toList
  | .defnDecl val =>
    let tyConsts := Expr.getUsedConstantsAsSet val.type
    let eqs ← TransforM.getEquationsFor val.name
    let allConsts := eqs.foldl (init := tyConsts) fun acc eq =>
      acc.insertMany eq.getUsedConstants
    return allConsts.toList
  | .inductDecl .. | .mutualDefnDecl ..  | .thmDecl .. | .quotDecl .. => unreachable!

def accumulateComponent (component : List Declaration) : TransforM Declaration := do
  match component with
  | [] => unreachable!
  | [decl] => return decl
  | decl :: decls =>
    match decl with
    | .inductDecl lparams nparams [ty] isUnsafe =>
      let types ← decls.foldlM (init := [ty]) fun acc decl => do
        let .inductDecl _ _ [ty] _ := decl | throwError "Invalid inductive while folding"
        return ty :: acc
      return .inductDecl lparams nparams types isUnsafe
    | .defnDecl val =>
      let defns ← decls.foldlM (init := [val]) fun acc decl => do
        let .defnDecl decl := decl | throwError "Invalid def while folding"
        return decl :: acc
      return .mutualDefnDecl defns
    | _ => throwError m!"Can't work with mutual decls {decl.getNames}"

public def addDeclsScc (decls : List Declaration) : TransforM Unit := do
  let mut declMap : Std.HashMap Name Declaration := {}
  let mut declDependencies : Std.HashMap Name (List Name) := {}
  for decl in decls do
    let declName := declarationName decl
    declMap := declMap.insert declName decl

  for decl in decls do
    let declName := declarationName decl
    let deps := (← declarationDependencies decl).filter declMap.contains
    declDependencies := declDependencies.insert declName deps

  let components := SCC.scc declMap.keys declDependencies.get!
  let decls ← components.mapM (fun comp => comp.map (declMap[·]!) |> accumulateComponent)
  decls.forM (liftM ∘ Lean.addDecl)

end Nunchaku
