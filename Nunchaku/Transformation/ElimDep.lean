module
public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model
import Nunchaku.Util.LocalContext
import Nunchaku.Util.AddDecls

namespace Nunchaku
namespace Transformation
namespace ElimDep

open Lean

structure DepState where
  argCache : Std.HashMap Name (Array Nat) := {}
  constCache : Std.HashMap Name Name := {}
  newEquations : Std.HashMap Name (List Expr) := {}

abbrev DepM := StateRefT DepState TransforM

def shouldElim (e : Expr) (elimAdditional : Bool) : MetaM Bool := do
  if ← Meta.isProof e then
    -- kill all proofs
    return true
  else if ← pure elimAdditional then
    let type ← Meta.inferType e
    if ← Meta.isPropFormerType type <||> Option.isNone <$> Meta.typeFormerTypeLevel type then
      -- In "additional" mode kill all props and non type former arguments as well
      return true
  return false

def argStencil (info : ConstantVal) : DepM (Array Nat) := do
  if let some stencil := (← get).argCache[info.name]? then
    return stencil

  let stencil ← Meta.forallTelescope info.type fun args dom => do
    let elimAdditional ←
      match dom with
      | .sort u =>
        if u.isAlwaysZero then
          pure false
        else if u.isNeverZero then
          pure true
        else
          throwError m!"Result type of {info.name} is Sort"
      | _ => pure false

    let mut drop := #[]
    for idx in 0...args.size do
      let arg := args[idx]!
      if ← shouldElim arg elimAdditional then
        drop := drop.push idx

    return drop

  modify fun s => { s with argCache := s.argCache.insert info.name stencil }
  return stencil

-- TODO: dedup with specialise
def elimCtorName (inductElimName : Name) (ctorName : Name) : MetaM Name := do
  let .str _ n := ctorName | throwError m!"Weird ctor name {ctorName}"
  return .str inductElimName n

mutual

def elimExpr (expr : Expr) (subst : Meta.FVarSubst) : DepM Expr := do
  match expr with
  | .const const us =>
    if TransforM.isBuiltin const then
      return .const const us
    sorry
  | .app .. => sorry
  | .lam .. =>
    Meta.lambdaBoundedTelescope expr 1 fun args body => do
      let arg := args[0]!
      if ← Meta.isProof arg then
        elimExpr body subst
      else
        let fvarId := arg.fvarId!
        let name ← fvarId.getUserName
        let bi ← fvarId.getBinderInfo
        let newType ← elimExpr (← fvarId.getType) subst

        Meta.withLocalDecl name bi newType fun replacedArg => do
          let newBody ← elimExpr body (subst.insert fvarId replacedArg)
          Meta.mkLambdaFVars #[replacedArg] newBody
  | .forallE .. =>
    -- TODO: not sure if we can do the same as lam and let here, seems trickier
    -- after all we don't want to throw away things such as implications inside of certain
    -- propositional expressions that we keep...
    sorry
  | .letE (nondep := nondep) .. =>
    Meta.letBoundedTelescope expr (some 1) fun args body => do
      let arg := args[0]!
      if ← Meta.isProof arg then
        elimExpr body subst
      else
        let fvarId := arg.fvarId!
        let name ← fvarId.getUserName
        let newType ← elimExpr (← fvarId.getType) subst
        let newValue ← elimExpr (← fvarId.getValue?).get! subst

        Meta.withLetDecl name newType newValue (nondep := nondep) fun replacedArg => do
          let newBody ← elimExpr body (subst.insert fvarId replacedArg)
          Meta.mkLetFVars #[replacedArg] newBody
  | .mdata _ e => elimExpr e subst
  | .proj .. => sorry
  | .fvar .. => return subst.apply expr
  | .lit .. | .sort .. | .bvar .. | .mvar .. => return expr

def elimForall (args : Array Expr) (body : Expr) (stencil : Array Nat) (idx : Nat) (acc : Array Expr)
    (subst : Meta.FVarSubst) : DepM Expr := do
  if h : idx < args.size then
    -- TODO: quadratic
    if stencil.contains idx then
      elimForall args body stencil (idx + 1) acc subst
    else
      let arg := args[idx]!
      let fvar := arg.fvarId!
      let newType ← elimExpr (← fvar.getType) subst
      Meta.withLocalDecl (← fvar.getUserName) (← fvar.getBinderInfo) newType fun newArg => do
        let subst := subst.insert fvar newArg
        elimForall args body stencil (idx + 1) (acc.push newArg) subst
  else
    let newBody ← elimExpr body subst
    let newExpr ← Meta.mkForallFVars acc newBody
    return newExpr

def elimConstType (expr : Expr) (stencil : Array Nat) : DepM Expr := do
  Meta.forallTelescope expr fun args dom => do
    elimForall args dom stencil 0 #[] {}

def elimCtor (inductElimName : Name) (ctorName : Name) : DepM Constructor := do
  let info ← getConstVal ctorName
  let elimName ← elimCtorName inductElimName ctorName
  return ⟨elimName, sorry⟩

def elimInduct (info : InductiveVal) : DepM Unit := do
  let name := info.name
  let elimName := (← get).constCache[name]!
  let stencil ← argStencil info.toConstantVal
  let newType ← elimConstType info.type stencil
  let newCtors ← info.ctors.mapM (elimCtor elimName)

  let decl := {
    name := elimName,
    type := newType,
    ctors := newCtors
  }

  TransforM.recordDecl <| .inductDecl sorry sorry [decl] false

  let inv := sorry
  TransforM.recordDecl <| .inductDecl sorry sorry [inv] false

def elimDefn (info : DefinitionVal) : DepM Unit := do
  let name := info.name
  let elimName := (← get).constCache[name]!
  if ← Meta.isProp info.type then
    throwError m!"Proofs should be erased but tried to work: {info.name}"

  let stencil ← argStencil info.toConstantVal
  let newType ← elimConstType info.type stencil

  let decl := {
    name := elimName,
    levelParams := info.levelParams,
    type := newType,
    value := mkApp (mkConst ``TransforM.sorryAx [sorry]) newType,
    safety := .safe,
    hints := .opaque,
  }

  TransforM.recordDecl <| .defnDecl decl
  let equations ← TransforM.getEquationsFor name
  let newEqs := sorry
  modify fun s => { s with newEquations := s.newEquations.insert elimName newEqs }

def elimAxiomOpaque (info : ConstantVal) : DepM Unit := do
  let name := info.name
  let elimName := (← get).constCache[name]!
  if ← Meta.isProp info.type then
    throwError m!"Proofs should be erased but tried to work: {info.name}"

  let stencil ← argStencil info
  let newType ← elimConstType info.type stencil

  let decl := {
    name := elimName,
    levelParams := info.levelParams,
    type := newType,
    isUnsafe := false
  }

  TransforM.recordDecl <| .axiomDecl decl

def elimTheorem (info : TheoremVal) : DepM Unit := do
  throwError m!"Proofs should be erased but tried to work: {info.name}"

def elimConst (name : Name) : DepM Name := do
  if let some name := (← get).constCache[name]? then
    return name
  else
    let elimName ← TransforM.mkFreshName name (pref := "elim_")
    modify fun s => { s with constCache := s.constCache.insert name elimName }
    trace[nunchaku.elimdep] m!"Working {name}"

    let info ← getConstInfo name
    match info with
    | .inductInfo info => elimInduct info
    | .defnInfo info => elimDefn info
    -- TODO: this requires a different naming scheme because ctors are prefixed
    | .ctorInfo info => sorry
    | .opaqueInfo info | .axiomInfo info => elimAxiomOpaque info.toConstantVal
    | .thmInfo info => elimTheorem info
    | .recInfo .. | .quotInfo .. =>
      throwError m!"Cannot elim dependent types in {name}"

    return elimName

end

def elim (g : MVarId) : DepM MVarId := do
  let g ← mapMVarId g elimExpr
  TransforM.replaceEquations (← get).newEquations
  TransforM.addDecls
  return g

public def transformation : Transformation MVarId MVarId LeanResult LeanResult where
   st := private Unit
   inner := private {
    name := "ElimDep"
    encode g := do
      let g ← elim g |>.run' {}
      trace[nunchaku.elimdep] m!"Result: {g}"
      return (g, ())
    decode _ res := return res
  }

end ElimDep
end Transformation
end Nunchaku
