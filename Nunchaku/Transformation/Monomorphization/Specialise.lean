module

public import Nunchaku.Transformation.Monomorphization.Util
import Nunchaku.Util.LocalContext
import Nunchaku.Util.AddDecls

namespace Nunchaku
namespace Transformation
namespace Monomorphization
namespace Specialise

open Lean

public structure SpecializeContext where
  solution : Std.HashMap FlowVariable (List GroundInput)

public structure SpecializeState where
  newEquations : Std.HashMap Name (List Expr) := {}
  specialisationCache : Std.HashMap (FlowVariable × GroundInput) Name := {}
  exprCache : Std.HashMap Expr Expr := {}

public structure DecodeCtx where
  decodeTable : Std.HashMap String (String × GroundInput)
  monoAnalysis : MonoAnalysisState

public abbrev SpecializeM := ReaderT SpecializeContext <| StateRefT SpecializeState MonoAnalysisM

public def SpecializeM.run (x : SpecializeM α) (ctx : SpecializeContext)
    (mono : MonoAnalysisState) : TransforM (α × DecodeCtx) := do
  let ((p, { specialisationCache := table, newEquations, .. }), monoAnalysis) ←
    StateRefT'.run (StateRefT'.run (ReaderT.run x ctx) {}) mono
  TransforM.replaceEquations newEquations
  TransforM.addDecls
  -- TODO: Deduplicate with Output
  let mut decodeTable := Std.HashMap.emptyWithCapacity table.size
  for ((kf, ka), v) in table do
    let v := v.toString
    if decodeTable.contains v then
        throwError "Non injective specialisation name mangling detected"
    decodeTable := decodeTable.insert v (kf.function.toString, ka)
  return (p, { decodeTable, monoAnalysis })

def levelParamsAsMeta (e : Expr) : MetaM Expr := do
  let params := Lean.collectLevelParams {} e |>.params
  let mut map := {}
  for param in params do
    map := map.insert param (← Meta.mkFreshLevelMVar)
  Core.transform e (post := post map)
where
  post (map : Std.HashMap Name Level) (e : Expr) : MetaM TransformStep := do
    match e with
    | .sort u =>
      return .done <| .sort <| replaceParams u map
    | .const name us =>
      return .done <| .const name (us.map (replaceParams · map))
    | _ => return .continue

  replaceParams (l : Level) (map : Std.HashMap Name Level) : Level :=
    l.substParams (fun p => some map[p]!)

def partitionMonoArgPositions (const : Name) (args : Array Expr) :
    MonoAnalysisM (Array Expr × Array (Expr × Nat)) := do
  let positions ← getMonoArgPositions const
  let mut others := #[]
  let mut targets := #[]
  for idx in 0...args.size do
    if let some posIdx := positions.findIdx? (· == idx) then
      targets := targets.push (args[idx]!, posIdx)
    else
      others := others.push args[idx]!

  return (others, targets)

partial def groundTypeOfExpr (expr : Expr) : MonoAnalysisM GroundTypeArg := do
  match expr with
  | .const const _ =>
    let positions ← getMonoArgPositions const
    if !positions.isEmpty then
      throwError m!"Underapplied constant cannot be used as ground type: {expr}"
    return .const const #[]
  | .app .. =>
    expr.withApp fun fn args => do
      match fn with
      | .const fn _ =>
        if TransforM.isBuiltin fn then
          throwError m!"Can't interpret {expr} as a ground type"
        let monoArgPositions ← getMonoArgPositions fn
        if monoArgPositions.isEmpty then
          return .const fn #[]
        let groundTypes ← monoArgPositions.mapM (fun idx => groundTypeOfExpr args[idx]!)
        return .const fn groundTypes
      | _ => throwError m!"Can't interpret {expr} as a ground type"
  | .mdata _ e => groundTypeOfExpr e
  | .forallE _ dom codom _ =>
    if !expr.isArrow then
      throwError m!"Can't interpret {expr} as a flow type"
    return .func (← groundTypeOfExpr dom) (← groundTypeOfExpr codom)
  | .proj .. | .lit .. | .sort .. | .bvar .. | .mvar .. | .letE .. | .lam ..
  | .fvar .. => throwError m!"Can't interpret {expr} as a ground type"

def instantiateStencilWith (remainder : Expr) (stencil : Array (Nat × GroundTypeArg))
      (stencilPos : Nat) (lastArgPos : Nat) : MetaM Expr := do
  if h : stencilPos < stencil.size then
    let (argPos, arg) := stencil[stencilPos]
    Meta.forallBoundedTelescope remainder (some (argPos - lastArgPos)) fun args body => do
      let argExpr ← arg.toExpr
      let .forallE _ type body _ := body | unreachable!
      trace[nunchaku.mono] m!"Instantiating arg of type {type} with {argExpr}"
      if !(← Meta.isDefEq (← Meta.inferType argExpr) type) then
        throwError m!"Failed to instantiate type argument {argExpr} for {type}"
      let body := body.instantiate1 argExpr
      let body ← instantiateStencilWith body stencil (stencilPos + 1) (argPos + 1)
      Meta.mkForallFVars args body
  else
    return remainder

def specialisedCtorName (inductSpecName : Name) (ctorName : Name) : MetaM Name := do
  let .str _ n := ctorName | throwError m!"Weird ctor name {ctorName}"
  return .str inductSpecName n

mutual

partial def specialiseExpr (expr : Expr) (subst : Meta.FVarSubst) : SpecializeM Expr := do
  if let some cached := (← get).exprCache[expr]? then
    return cached
  else
    let finishedExpr ← specialiseExprRaw expr subst
    modify fun s => { s with exprCache := s.exprCache.insert expr finishedExpr }
    return finishedExpr

partial def specialiseExprRaw (expr : Expr) (subst : Meta.FVarSubst) : SpecializeM Expr := do
  match expr with
  | .const const us =>
    if TransforM.isBuiltin const then
      return .const const us
    let positions ← getMonoArgPositions const
    if !positions.isEmpty then
      throwError m!"Underapplied constant cannot be monomorphised: {expr}"

    match ← getConstInfo const with
    | .ctorInfo info =>
      let pattern : FlowVariable × GroundInput := ⟨⟨info.induct⟩, ⟨#[]⟩⟩
      specialiseConst info.induct pattern.2
      let specialisedInductName := (← get).specialisationCache[pattern]!
      let specialisedName ← specialisedCtorName specialisedInductName info.name
      return .const specialisedName []
    | .inductInfo info | .defnInfo info | .axiomInfo info | .opaqueInfo info =>
      let pattern : FlowVariable × GroundInput := ⟨⟨info.name⟩, ⟨#[]⟩⟩
      specialiseConst const pattern.2
      let specialisedName := (← get).specialisationCache[pattern]!
      return .const specialisedName []
    | .recInfo .. | .quotInfo .. | .thmInfo .. =>
      throwError m!"Cannot monomorphise {expr}"
  | .app .. =>
    expr.withApp fun fn args => do
      match fn with
      | .const fn us =>
        if TransforM.isBuiltin fn then
          let args ← args.mapM (specialiseExpr · subst)
          return mkAppN (.const fn us) args
        else
          match ← getConstInfo fn with
          | .ctorInfo info =>
            let (others, targets) ← partitionMonoArgPositions info.name args
            let pattern : FlowVariable × GroundInput :=
              ⟨⟨info.induct⟩, ⟨← targets.mapM (fun (e, _) => groundTypeOfExpr e)⟩⟩
            specialiseConst info.induct pattern.2
            let specialisedInductName := (← get).specialisationCache[pattern]!
            let remainingArgs ← others.mapM (specialiseExpr · subst)
            let specialisedName ← specialisedCtorName specialisedInductName info.name
            return mkAppN (.const specialisedName []) remainingArgs
          -- TODO: opaques need some additional treatment
          | .inductInfo info | .defnInfo info | .axiomInfo info | .opaqueInfo info =>
            let (others, targets) ← partitionMonoArgPositions info.name args
            let pattern : FlowVariable × GroundInput :=
              ⟨⟨info.name⟩, ⟨← targets.mapM (fun (e, _) => groundTypeOfExpr e)⟩⟩
            specialiseConst fn pattern.2
            let specialisedName := (← get).specialisationCache[pattern]!
            let remainingArgs ← others.mapM (specialiseExpr · subst)
            return mkAppN (.const specialisedName []) remainingArgs
          | .recInfo .. | .quotInfo .. | .thmInfo .. =>
            throwError m!"Cannot monomorphise {expr}"
      | _ =>
        let args ← args.mapM (specialiseExpr · subst)
        return mkAppN (← specialiseExpr fn subst) args
  | .lam .. =>
    Meta.lambdaBoundedTelescope expr 1 fun args body => do
      let arg := args[0]!
      let fvarId := arg.fvarId!
      let name ← fvarId.getUserName
      let bi ← fvarId.getBinderInfo
      let newType ← specialiseExpr (← fvarId.getType) subst

      Meta.withLocalDecl name bi newType fun replacedArg => do
        let newBody ← specialiseExpr body (subst.insert fvarId replacedArg)
        Meta.mkLambdaFVars #[replacedArg] newBody
  | .forallE .. =>
    Meta.forallBoundedTelescope expr (some 1) fun args body => do
      let arg := args[0]!
      let fvarId := arg.fvarId!
      let name ← fvarId.getUserName
      let bi ← fvarId.getBinderInfo
      let newType ← specialiseExpr (← fvarId.getType) subst

      Meta.withLocalDecl name bi newType fun replacedArg => do
        let newBody ← specialiseExpr body (subst.insert fvarId replacedArg)
        Meta.mkForallFVars #[replacedArg] newBody
  | .letE (nondep := nondep) .. =>
    Meta.letBoundedTelescope expr (some 1) fun args body => do
      let arg := args[0]!
      let fvarId := arg.fvarId!
      let name ← fvarId.getUserName
      let newType ← specialiseExpr (← fvarId.getType) subst
      let newValue ← specialiseExpr (← fvarId.getValue? (allowNondep := true)).get! subst

      Meta.withLetDecl name newType newValue (nondep := nondep) fun replacedArg => do
        let newBody ← specialiseExpr body (subst.insert fvarId replacedArg)
        Meta.mkLetFVars (generalizeNondepLet := false) #[replacedArg] newBody
  | .mdata _ e => specialiseExpr e subst
  | .proj _ idx struct =>
    let structType ← Meta.inferType struct
    let specialisedType ← specialiseExpr structType subst
    let .const specialisedName [] := specialisedType | throwError m!"Cannot specialise {expr}"
    let specialisedStruct ← specialiseExpr struct subst
    -- Specialisation currently only modifies parameters -> proj indices are unaffected
    return .proj specialisedName idx specialisedStruct
  | .fvar .. => return subst.apply expr
  | .lit .. | .sort .. | .bvar .. | .mvar .. => return expr

partial def specialiseConstType (info : ConstantVal) (input : GroundInput) :
    SpecializeM (Expr × Level) := do
  let expr ← Meta.mkConstWithFreshMVarLevels info.name
  let type ← Meta.inferType expr
  let positions ← getMonoArgPositions info.name
  assert! positions.size = input.args.size
  let stencil := positions.zip input.args
  let instantiated ← instantiateStencilWith type stencil 0 0
  let final ← instantiateMVars instantiated
  let level ← Meta.getLevel final
  let specialised ← specialiseExpr final {}
  return (specialised, level)

partial def specialiseCtor (inductSpecName : Name) (ctorName : Name) (input : GroundInput) :
    SpecializeM Constructor := do
  let info ← getConstVal ctorName
  let specName ← specialisedCtorName inductSpecName ctorName
  let (specType, _) ← specialiseConstType info input
  return ⟨specName, specType⟩

partial def specialiseInduct (info : InductiveVal) (input : GroundInput) : SpecializeM Unit := do
  let name := info.name
  let specName := (← get).specialisationCache[(FlowVariable.mk name, input)]!
  let (specType, _) ← specialiseConstType info.toConstantVal input
  let newCtors ← info.ctors.mapM (specialiseCtor specName · input)
  trace[nunchaku.mono] m!"Proposing {specType} {newCtors.map (·.type)}"

  let decl := {
    name := specName,
    type := specType,
    ctors := newCtors
  }
  let nparams := info.numParams - (← getMonoArgPositions name).size
  for (oldCtor, newCtor) in info.ctors.zip newCtors do
    modify fun s =>
      { s with specialisationCache := s.specialisationCache.insert (⟨oldCtor⟩, input) newCtor.name }
  TransforM.recordDerivedDecl name <| .inductDecl [] nparams [decl] false

partial def specialiseEquation (name : Name) (eq : Expr) (input : GroundInput) :
    SpecializeM Expr := do
  if input.args.isEmpty then
    specialiseExpr eq {}
  else
    let eq ← levelParamsAsMeta eq
    let positions ← getMonoArgPositions name
    assert! positions.size = input.args.size
    let stencil := positions.zip input.args
    let instantiated ← instantiateStencilWith eq stencil 0 0
    let final ← instantiateMVars instantiated
    specialiseExpr final {}

partial def specialiseOpaque (info : OpaqueVal) (input : GroundInput) : SpecializeM Unit := do
  let name := info.name
  let specName := (← get).specialisationCache[(FlowVariable.mk name, input)]!
  let (specType, u) ← specialiseConstType info.toConstantVal input

  let defn := {
    name := specName,
    levelParams := [],
    type := specType,
    value := TransforM.mkSorryAx specType u,
    isUnsafe := info.isUnsafe
  }
  TransforM.recordDerivedDecl name <| .opaqueDecl defn

partial def specialiseAxiom (info : AxiomVal) (input : GroundInput) : SpecializeM Unit := do
  let name := info.name
  let specName := (← get).specialisationCache[(FlowVariable.mk name, input)]!
  let (specType, _) ← specialiseConstType info.toConstantVal input

  let defn := {
    name := specName,
    levelParams := [],
    type := specType,
    isUnsafe := info.isUnsafe
  }
  TransforM.recordDerivedDecl name <| .axiomDecl defn

partial def specialiseDefn (info : DefinitionVal) (input : GroundInput) : SpecializeM Unit := do
  let name := info.name
  let specName := (← get).specialisationCache[(FlowVariable.mk name, input)]!
  let (specType, u) ← specialiseConstType info.toConstantVal input

  trace[nunchaku.mono] m!"Proposing {specType}"

  let defn := {
    name := specName,
    levelParams := [],
    type := specType,
    value := TransforM.mkSorryAx specType u,
    hints := .opaque,
    safety := .safe
  }
  TransforM.recordDerivedDecl name <| .defnDecl defn

  let equations ← TransforM.getEquationsFor name
  let newEqs ← equations.mapM (specialiseEquation name · input)
  modify fun s => { s with newEquations := s.newEquations.insert specName newEqs }

partial def specialiseConst (name : Name) (input : GroundInput) : SpecializeM Unit := do
  let flow := FlowVariable.mk name
  if (← get).specialisationCache.contains (flow, input) then
    return ()
  else
    let specName ← TransforM.mkFreshName name (pref := "spec_")
    modify fun s =>
      { s with specialisationCache := s.specialisationCache.insert (flow, input) specName }

    trace[nunchaku.mono] m!"Specialising {name} for {input} as {specName}"

  let info ← getConstInfo name
  match info with
  | .inductInfo info => specialiseInduct info input
  | .defnInfo info => specialiseDefn info input
  | .ctorInfo .. => return ()
  | .opaqueInfo info => specialiseOpaque info input
  | .axiomInfo info => specialiseAxiom info input
  | _ => unreachable!

  trace[nunchaku.mono] m!"Specialising {name} for {input} done"

end

public partial def specialize (g : MVarId) : SpecializeM MVarId := do
  for (var, inputs) in (← read).solution do
    for input in inputs do
      specialiseConst var.function input

  trace[nunchaku.mono] m!"Specialising in {g}"
  let g ← mapMVarId g specialiseExpr
  return g

end Specialise
end Monomorphization
end Transformation
end Nunchaku
