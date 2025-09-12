module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model
import Nunchaku.Util.LocalContext
import Nunchaku.Util.AddDecls
import Lean.Meta.Tactic.Clear

/-!
This module contains the transformation for eliminating comfort features from Lean, in particular:
- universe parameters by instantiating them with `0`
- let declarations by ζ reduction
- lambdas by lambda lifting TODO

TODO: currently this is only done in the goal and in equations, we might also need to do this in
other type definitions

TODO: right before emitting the raw problem to nunchaku we might be better of globally sharing with
lets so we don't produce an exponential problem.
-/

namespace Nunchaku
namespace Transformation
namespace ElimComfort

open Lean

structure ComfortState where
  nameIdx : Nat := 0
  decls : List Declaration := {}
  consts : Std.HashMap Name Name := {}

abbrev ComfortM := StateRefT ComfortState TransforM

def ComfortM.run (x : ComfortM α) : TransforM (α × ComfortState) :=
  StateRefT'.run x {}

def zetaBetaReduce (e : Expr) : MetaM Expr := do
  let e ← Meta.zetaReduce e
  Core.betaReduce e

def isTypeAlias (const : Name) : MetaM Bool := do
  let .defnInfo info ← getConstInfo const | return false
  if !(← Meta.isTypeFormerType info.type) then return false
  let reducedValue ← zetaBetaReduce info.value
  Meta.lambdaTelescope reducedValue fun _ body => do
    let body := body.consumeMData
    match body with
    | .fvar .. | .forallE .. | .sort .. => return true
    | .const name .. => return (← Meta.isTypeFormerType (← getConstVal name).type)
    | .proj .. => return false
    | .app .. => return body.getAppFn.isConst
    | .mdata .. | .lit .. | .mvar .. | .letE .. | .lam .. | .bvar .. => unreachable!

def unfoldTypeAliases (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := pre)
where
  pre (expr : Expr) : MetaM TransformStep := do
    let .const name _ := expr.getAppFn | return .continue
    if ! (← isTypeAlias name) then return .continue
    let some expr ← Meta.unfoldDefinition? expr (ignoreTransparency := true)
      | throwError m!"Failed to unfold type alias {expr}"
    return .visit expr

def recordName (orig : Name) (new : Name) : ComfortM Unit :=
  modify fun s => { s with consts := s.consts.insert orig new }

def getNewName! (orig : Name) : ComfortM Name := do
  return (← get).consts[orig]!

-- TODO: generalize with specialize
def mkFreshName (name : Name) : ComfortM Name := do
  let idx := (← get).nameIdx
  let freshName := Name.str name s!"_{idx}"
  modify fun s => { s with nameIdx := s.nameIdx + 1 }
  recordName name freshName
  return freshName

def recordDecl (decl : Declaration) : ComfortM Unit :=
  modify fun s => { s with decls := decl :: s.decls }

mutual

partial def elimConst (const : Name) : ComfortM Name := do
  if let some name := (← get).consts[const]? then
    return name

  if TransforM.isBuiltin const then
    return const

  match ← getConstInfo const with
  | .defnInfo info =>
    let freshName ← mkFreshName const
    let u ← Meta.getLevel info.type
    let type ← elimComfortExpr info.type
    let decl := {
      name := freshName,
      levelParams := info.levelParams,
      type := type,
      value := mkApp (mkConst ``TransforM.sorryAx [u]) type,
      hints := info.hints,
      safety := .safe
    }
    recordDecl <| .defnDecl decl
    return freshName
  | .inductInfo info =>
    let freshName ← mkFreshName const
    let ctors ← info.ctors.mapM fun ctorName => do
      let .str _ n := ctorName | throwError m!"Weird ctor name {ctorName}"
      let freshCtorName := .str freshName n
      recordName ctorName freshCtorName
      let type ← elimComfortExpr (← getConstVal ctorName).type
      return { name := freshCtorName, type := type }
    let type ← elimComfortExpr info.type
    let decl := {
      name := freshName,
      type := type,
      ctors := ctors
    }
    recordDecl <| .inductDecl info.levelParams info.numParams [decl] info.isUnsafe
    return freshName

  | .axiomInfo info | .opaqueInfo info | .thmInfo info =>
    let freshName ← mkFreshName const
    let type ← elimComfortExpr info.type
    let decl := {
      name := freshName,
      levelParams := info.levelParams,
      type := type,
      isUnsafe := false
    }
    recordDecl <| .axiomDecl decl
    return freshName
  | .ctorInfo info =>
    discard <| elimConst info.induct
    getNewName! const
  | .recInfo info =>
    discard <| elimConst info.getMajorInduct
    getNewName! const
  | .quotInfo .. => return const

partial def elimComfortExpr (e : Expr) : ComfortM Expr := do
  let e ← unfoldTypeAliases e
  let e ← zetaBetaReduce e
  Core.transform e (pre := pre)
where
  pre (e : Expr) : ComfortM TransformStep := do
    let .const name us := e | return .continue
    let name ← elimConst name
    return .done <| .const name us

end

/--
This function eliminates:
- unfolds all type alises
- universe parameters by instanting them with `0`
- applies ζ and β reduction
-/
def elimComfortUniv (e : Expr) (subst : Meta.FVarSubst) : ComfortM Expr := do
  let e ← elimComfortExpr e
  Meta.transform e (pre := pre subst)
where
  pre (subst : Meta.FVarSubst) (e : Expr) : ComfortM TransformStep := do
    match e with
    | .sort u =>
      return .done <| .sort <| killParams u
    | .const name us =>
      return .done <| .const name (us.map killParams)
    | .fvar .. => return .done <| subst.apply e
    | _ => return .continue

  killParams (l : Level) : Level :=
    Level.ofNat <| killParamsAux l

  killParamsAux (l : Level) : Nat :=
    match l with
    | .zero => 0
    | .succ l => killParamsAux l + 1
    | .max l r => max (killParamsAux l) (killParamsAux r)
    | .imax l r =>
      let r := killParamsAux r
      if r == 0 then
        0
      else
        max (killParamsAux l) r
    | .param _ => 0
    | .mvar .. => unreachable!

def encode (g : MVarId) : ComfortM MVarId := g.withContext do
  let g ← mapMVarId g elimComfortUniv (processLetDecl := true)
  g.withContext do
    let mut lets := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then
        continue
      if decl.isLet then
        lets := lets.push decl.fvarId
    let g ← g.tryClearMany lets

    let equations ← TransforM.getEquations
    let mut newEquations := {}
    for (name, eqs) in equations do
      if ← isTypeAlias name then
        continue
      let eqs ← eqs.mapM (liftM ∘ elimComfortExpr)
      let newName := (← get).consts.getD name name
      newEquations := newEquations.insert newName eqs

    TransforM.replaceEquations newEquations
    return g

public def transformation : Transformation MVarId MVarId LeanResult LeanResult where
   st := private Unit
   inner := private {
    name := "ElimComfort"
    encode g := do
      let (g, st) ← ComfortM.run <| encode g
      addDeclsScc st.decls
      return (g, ())
    decode _ res := return res
  }

end ElimComfort
end Transformation
end Nunchaku
