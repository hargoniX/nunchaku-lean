module
public import Chako.Transformation.ElimDep.Basic
import Chako.Util.AuxiliaryConsts
import Lean.Meta.Match.MatchEqs

namespace Chako
namespace Transformation
namespace ElimDep

open Lean

def specialiseParamsAndMotive (body : Expr) (params : Array Expr) (motive : Expr)
    (remainingParams : Nat := params.size) : MetaM Expr := do
  trace[chako] m!"Specialising {remainingParams} binders in {body} for {params} and {motive}"
  match remainingParams with
  | 0 =>
    let body ← instantiateBinder body motive
    let body ← Core.betaReduce body
    instantiateMVars body
  | remainingParams@(n + 1) =>
    let param := params[params.size - remainingParams]!
    let body ← instantiateBinder body param
    specialiseParamsAndMotive body params motive n
where
  instantiateBinder (body : Expr) (param : Expr) : MetaM Expr := do
    let .forallE _ type body _ := body | unreachable!
    let paramType ← Meta.inferType param
    trace[chako] m!"Trying to instantiate binder {type} with {param} : {paramType}"
    if !(← Meta.isDefEq type paramType) then
      throwError m!"Failed to instantiate motive argument {param} for {type}"
    let body := body.instantiate1 param
    return body

def specialiseMatcherLikeEquationFor (elimFn : Expr) (params : Array Expr) (motive : Expr)
      (baseEq : Expr) : MetaM Expr := do
    let specialisedEq ← specialiseParamsAndMotive baseEq params motive
    Meta.forallTelescope specialisedEq fun arguments eq => do
      let_expr Eq _ lhs rhs := eq | unreachable!
      let lhsArgs := lhs.getAppArgs
      let lhsArgs := lhsArgs.drop (params.size + 1)
      let lhs := mkAppN elimFn lhsArgs
      let eq ← Meta.mkEq lhs rhs
      let body ← Meta.mkForallFVars arguments eq
      Meta.mkForallFVars elimFn.getAppArgs body

def mkCasesOnEquationForCtor (info : InductiveVal) (origFn : Name) (ctorIdx : Nat) : MetaM Expr := do
  let origType ← Meta.inferType (← Meta.mkConstWithFreshMVarLevels origFn)
  Meta.forallBoundedTelescope origType (some info.numParams) fun params body => do
  Meta.forallBoundedTelescope body (some 1) fun motive body => do
  let motive := motive[0]!
  Meta.forallBoundedTelescope body (some info.numIndices) fun _ body => do
  -- Skip the discriminant, we construct it ourselves
  let .forallE _ _ body _ := body | unreachable!
  Meta.forallTelescope body fun alts _ => do
    let alt := alts[ctorIdx]!
    Meta.forallTelescope (← Meta.inferType alt) fun altArgs resType => do
      let motiveArgs := resType.getAppArgs
      let indices := motiveArgs[0...(motiveArgs.size - 1)].toArray
      let discr := motiveArgs[motiveArgs.size - 1]!
      let lhsArgs := params ++ #[motive] ++ indices ++ #[discr] ++ alts
      let lhs ← Meta.mkAppOptM origFn (lhsArgs.map Option.some) 
      let rhs := mkAppN alt altArgs
      let eq ← Meta.mkEq lhs rhs
      Meta.mkForallFVars (params ++ #[motive] ++ alts ++ altArgs) eq

public partial def mkAuxiliaryCasesOn (fn : Name) (params : Array Expr) (motive : Expr)
    (info : InductiveVal) : DepM Expr := do
  match (← get).matchLikeCache[(fn, params, motive)]? with
  | some fn => return fn
  | none =>
    let expr ← Meta.mkConstWithFreshMVarLevels fn
    let type ← Meta.inferType expr
    let specialisedType ← specialiseParamsAndMotive type params motive
    let u ← Meta.getLevel specialisedType
    if u.hasMVar then
      throwError m!"Level has mvar after specialising {fn} on {params} and {motive}: {u}"
    let elimName ← TransforM.mkFreshName fn (pref := "casesOn_elim_")

    let newFn ← Meta.mkAuxDefinition (compile := false)
      elimName
      specialisedType
      (TransforM.mkSorryAx specialisedType u)

    let baseEqns ← info.ctors.mapIdxM (fun idx _ => mkCasesOnEquationForCtor info fn idx)
    let eqns ← liftM <| baseEqns.mapM (specialiseMatcherLikeEquationFor newFn params motive)
    TransforM.injectEquations elimName eqns

    trace[chako.elimdep] m!"Created auxiliary casesOn: {newFn}, eqns: {eqns}"
    modify fun s => { s with matchLikeCache := s.matchLikeCache.insert (fn, params, motive) newFn }
    return newFn

public partial def mkAuxiliaryMatcher (fn : Name) (params : Array Expr) (motive : Expr) :
    DepM Expr := do
  match (← get).matchLikeCache[(fn, params, motive)]? with
  | some fn => return fn
  | none =>
    let expr ← Meta.mkConstWithFreshMVarLevels fn
    let type ← Meta.inferType expr
    let specialisedType ← specialiseParamsAndMotive type params motive
    let u ← Meta.getLevel specialisedType
    if u.hasMVar then
      throwError m!"Level has mvar after specialising {fn} on {params} and {motive}: {u}"
    let elimName ← TransforM.mkFreshName fn (pref := "match_elim_")

    let newFn ← Meta.mkAuxDefinition (compile := false)
      elimName
      specialisedType
      (TransforM.mkSorryAx specialisedType u)

    let eqns := (← Meta.Match.getEquationsForImpl fn).eqnNames
    let newEqns ← liftM <| eqns.mapM fun eqn => do
      let eqn ← Meta.inferType (← Meta.mkConstWithFreshMVarLevels eqn)
      specialiseMatcherLikeEquationFor newFn params motive eqn
    TransforM.injectEquations elimName newEqns.toList

    trace[chako.elimdep] m!"Created auxiliary matcher: {newFn}, eqns: {newEqns}"
    modify fun s => { s with matchLikeCache := s.matchLikeCache.insert (fn, params, motive) newFn }
    return newFn

def mkAuxiliaryUnitType (lvl : Level) : DepM Name := do
  let some lvl := lvl.toNat | throwError "Non constant level in PUnit occurence"
  match (← get).unitCache[lvl]? with
  | some type => return type
  | none =>
    let elimName ← TransforM.mkFreshName ``PUnit (pref := "punit_elim")
    addDecl <| .inductDecl [] 0 (isUnsafe := false) [{
      name := elimName,
      type := .sort (.ofNat lvl),
      ctors := [{ name := elimName ++ auxiliaryUnitCtor, type := mkConst elimName [] }]
    }]
    modify fun s => { s with unitCache := s.unitCache.insert lvl elimName }
    return elimName

def mkAuxiliaryUnitValue (lvl : Level) : DepM Name := do
  let type ← mkAuxiliaryUnitType lvl
  return type ++ auxiliaryUnitCtor

public partial def preEliminateConst (const : Name) (us : List Level) :
    DepM (Option (Name × List Level)) := do
  match const with
  | ``PUnit =>
    let [lvl] := us | throwError m!"Type incorrect PUnit"
    return some <| ((← mkAuxiliaryUnitType lvl), [])
  | ``PUnit.unit =>
    let [lvl] := us | throwError m!"Type incorrect PUnit.unit"
    return some <| ((← mkAuxiliaryUnitValue lvl), [])
  | ``Unit.unit =>
    return some <| ((← mkAuxiliaryUnitValue 1), [])
  | _ => return none

public partial def preEliminateApp (fn : Name) (us : List Level) (args : Array Expr) :
    DepM (Option Expr) := do
  match fn with
  | ``ite =>
    let lvl := us[0]!
    let α := args[0]!
    let p := args[1]!
    let thenE := args[3]!
    let elseE := args[4]!
    return some <| mkApp4 (mkConst ``classicalIf [lvl]) α p thenE elseE
  | ``dite =>
    let lvl := us[0]!
    let α := args[0]!
    let p := args[1]!
    let thenE := mkApp args[3]! (TransforM.mkSorryAx p 0)
    let elseE := mkApp args[4]! (TransforM.mkSorryAx (mkNot p) 0)
    return some <| mkApp4 (mkConst ``classicalIf [lvl]) α p thenE elseE
  | ``Decidable.decide =>
    let p := args[0]!
    let α := mkApp (mkConst ``Decidable) p
    let thenE := mkConst ``Bool.true
    let elseE := mkConst ``Bool.false
    return some <| mkApp4 (mkConst ``classicalIf [1]) α p thenE elseE
  | ``panic | ``panicCore | ``panicWithPos | ``panicWithPosWithDecl =>
    let lvl := us[0]!
    let α := args[0]!
    let inst := args[1]!
    return some <| mkApp2 (mkConst ``Inhabited.default [lvl]) α inst
  | ``False.rec =>
    let motive := args[0]!
    let .lam _ _ body _ := motive |
      throwError m!"Don't know how to encode False.rec with {args}"
    if body.hasLooseBVars then
      throwError m!"Don't know how to encode False.rec with {args}"
    return some <| TransforM.mkSorryAx body us[0]!
  | _ => return none

public def argIsCtorIrrelevant (ctorStencil : Array ArgKind) (inductInfo : InductiveVal) (idx : Nat) :
    DepM Bool := do
  if idx < inductInfo.numParams then
    let inductStencil ← argStencil inductInfo.toConstantVal
    return inductStencil[idx]!.isInductiveErasable
  else
    return ctorStencil[idx]!.isProof

public def filterCtorArgs (ctorStencil : Array ArgKind) (inductInfo : InductiveVal) (xs : Array α) :
    DepM (Array α) := do
  let mut new := #[]
  for h : idx in 0...xs.size do
    if !(← argIsCtorIrrelevant ctorStencil inductInfo idx) then
      let arg := xs[idx]
      new := new.push arg
  return new

end ElimDep
end Transformation
end Chako
