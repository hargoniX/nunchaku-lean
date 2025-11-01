module
import Lean.Util.SCC
public import Lean.AddDecl
public import Chako.Util.TransforM

namespace Chako

open Lean Core

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

def addComponent (component : List Declaration) : TransforM Unit := do
  trace[nunchaku] m!"Adding {component.map (·.getTopLevelNames)}"
  match component with
  | [] => unreachable!
  | [decl] => addDecl decl
  | decl :: decls =>
    match decl with
    | .inductDecl lparams nparams [ty] isUnsafe =>
      let types ← decls.foldlM (init := [ty]) fun acc decl => do
        let .inductDecl _ _ [ty] _ := decl | throwError "Invalid inductive while folding"
        return ty :: acc
      addDecl <| .inductDecl lparams nparams types isUnsafe
    | .defnDecl .. =>
      -- We're not actually adding bodies or anything so we can just add them 1 by 1
      addDecl decl
      decls.forM (liftM ∘ addDecl)
    | _ => throwError m!"Can't work with mutual decls {decl.getNames}"

def declsScc (decls : List Declaration) : TransforM (List (List Declaration)) := do
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
  return components.map (fun comp => comp.map (declMap[·]!))

public def addDeclsScc (decls : List Declaration) : TransforM Unit := do
  let components ← declsScc decls
  components.forM addComponent

namespace TransforM

public def addAttribute (decl : Name) (attr : NunAttribute) : TransforM Unit :=
  modify fun s => { s with
    attributes := s.attributes.alter decl fun | some s => s.insert attr | none => some { attr }
  }

public def getAttributes (decl : Name) : TransforM (Std.TreeSet NunAttribute) :=
  return (← get).attributes.getD decl {}

public def recordNewDecl (decl : Declaration) : TransforM Unit :=
  modify fun s => { s with freshDecls := decl :: s.freshDecls }

public def recordDerivedDecl (orig : Name) (decl : Declaration) : TransforM Unit := do
  recordNewDecl decl
  let name := decl.getNames.head!
  modify fun s => { s with attributes := s.attributes.insert name (s.attributes.getD orig {}) }

public def addDecls : TransforM Unit := do
  let decls := (← get).freshDecls
  addDeclsScc decls
  modify fun s => { s with freshDecls := [] }

end TransforM

end Chako
