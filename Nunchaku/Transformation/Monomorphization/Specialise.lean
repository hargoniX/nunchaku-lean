module

public import Nunchaku.Transformation.Monomorphization.Util
import Nunchaku.Util.LocalContext

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
  nameIdx : Nat := 0

public abbrev SpecializeM := ReaderT SpecializeContext <| StateRefT SpecializeState MonoAnalysisM

public def SpecializeM.run (x : SpecializeM α) (ctx : SpecializeContext)
    (mono : MonoAnalysisState) : TransforM (α × SpecializeState) := do
  let (p, _) ← StateRefT'.run (StateRefT'.run (ReaderT.run x ctx) {}) mono
  return p

def metaLevels (e : Expr) : MetaM Expr := do
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

def mkFreshSpecName (name : Name) : SpecializeM Name := do
  let idx := (← get).nameIdx
  modify fun s => { s with nameIdx := s.nameIdx + 1}
  return Name.str name s!"spec_{idx}"

public partial def specialize (g : MVarId) : SpecializeM MVarId := do
  for (var, inputs) in (← read).solution do
    for input in inputs do
      specialiseConst var.function input

  trace[nunchaku.mono] m!"Specialising in {g}"
  let g ← mapMVarId g specialiseExpr
  return g
where
  partitionMonoArgPositions (const : Name) (args : Array Expr) :
      SpecializeM (Array Expr × Array (Expr × Nat)) := do
    let positions ← getMonoArgPositions const
    let mut others := #[]
    let mut targets := #[]
    for idx in 0...args.size do
      if let some posIdx := positions.findIdx? (· == idx) then
        targets := targets.push (args[idx]!, posIdx)
      else
        others := others.push args[idx]!

    return (others, targets)

  groundTypeOfExpr (expr : Expr) : SpecializeM GroundTypeArg := do
    match expr with
    | .const const us =>
      let positions ← getMonoArgPositions const
      if !positions.isEmpty then
        throwError m!"Underapplied constant cannot be used as ground type: {expr}"
      return .const const us #[]
    | .app .. =>
      expr.withApp fun fn args => do
        match fn with
        | .const fn us =>
          if TransforM.isBuiltin fn then
            throwError m!"Can't interpret {expr} as a ground type"
          let monoArgPositions ← getMonoArgPositions fn
          if monoArgPositions.isEmpty then
            return .const fn us #[]
          let groundTypes ← monoArgPositions.mapM (fun idx => groundTypeOfExpr args[idx]!)
          return .const fn us groundTypes
        | _ => throwError m!"Can't interpret {expr} as a ground type"
    | .mdata _ e => groundTypeOfExpr e
    | .proj .. | .lit .. | .sort .. | .bvar .. | .mvar .. | .forallE .. | .letE .. | .lam ..
    | .fvar .. => throwError m!"Can't interpret {expr} as a ground type"

  specialiseExpr (expr : Expr) (subst : Meta.FVarSubst) : SpecializeM Expr := do
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
      | .inductInfo info | .defnInfo info =>
        let pattern : FlowVariable × GroundInput := ⟨⟨info.name⟩, ⟨#[]⟩⟩
        specialiseConst const pattern.2
        let specialisedName := (← get).specialisationCache[pattern]!
        return .const specialisedName []
      | .axiomInfo .. | .opaqueInfo .. => return expr
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
            | .inductInfo info | .defnInfo info =>
              let (others, targets) ← partitionMonoArgPositions info.name args
              let pattern : FlowVariable × GroundInput :=
                ⟨⟨info.name⟩, ⟨← targets.mapM (fun (e, _) => groundTypeOfExpr e)⟩⟩
              specialiseConst fn pattern.2
              let specialisedName := (← get).specialisationCache[pattern]!
              let remainingArgs ← others.mapM (specialiseExpr · subst)
              return mkAppN (.const specialisedName []) remainingArgs
            | .axiomInfo .. | .opaqueInfo .. =>
              let args ← args.mapM (specialiseExpr · subst)
              return mkAppN (.const fn us) args
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
        let newValue ← specialiseExpr (← fvarId.getValue?).get! subst

        Meta.withLetDecl name newType newValue (nondep := nondep) fun replacedArg => do
          let newBody ← specialiseExpr body (subst.insert fvarId replacedArg)
          Meta.mkLetFVars #[replacedArg] newBody
    | .mdata _ e => specialiseExpr e subst
    | .proj typeName idx struct =>
      let structType ← Meta.inferType struct
      let specialisedType ← specialiseExpr structType subst
      let .const specialisedName [] := specialisedType | throwError m!"Cannot specialise {expr}"
      let specialisedStruct ← specialiseExpr struct subst
      -- Specialisation currently only modifies parameters -> proj indices are unaffected
      return .proj specialisedName idx specialisedStruct
    | .fvar .. => return subst.apply expr
    | .lit .. | .sort .. | .bvar .. | .mvar .. => return expr

  specialiseConstTypeAux (remainder : Expr) (stencil : Array (Nat × GroundTypeArg))
      (stencilPos : Nat) (lastArgPos : Nat) : SpecializeM Expr := do
    if h : stencilPos < stencil.size then
      let (argPos, arg) := stencil[stencilPos]
      Meta.forallBoundedTelescope remainder (some (argPos - lastArgPos - 1)) fun args body => do
        let argExpr := arg.toExpr
        let .forallE _ type body _ := body | unreachable!
        if !(← Meta.isDefEq (← Meta.inferType argExpr) type) then
          throwError m!"Failed to instantiate type argument {argExpr} for {type}"
        let body := body.instantiate1 argExpr
        let body ← specialiseConstTypeAux body stencil (stencilPos + 1) argPos
        Meta.mkForallFVars args body
    else
      return remainder

  specialiseConstType (info : ConstantVal) (input : GroundInput) : SpecializeM Expr := do
    let expr ← Meta.mkConstWithFreshMVarLevels info.name
    let type ← Meta.inferType expr
    let positions ← getMonoArgPositions info.name
    assert! positions.size = input.args.size
    let stencil := positions.zip input.args
    let instantiated ← specialiseConstTypeAux type stencil 0 0
    let final ← instantiateMVars instantiated
    specialiseExpr final {}

  specialiseConst (name : Name) (input : GroundInput) : SpecializeM Unit := do
    let flow := FlowVariable.mk name
    if (← get).specialisationCache.contains (flow, input) then
      return ()
    else
      -- TODO: better name generator
      let specName ← mkFreshSpecName name
      modify fun s =>
        { s with specialisationCache := s.specialisationCache.insert (flow, input) specName }

      trace[nunchaku.mono] m!"Specialising {name} for {input} as {specName}"

    let info ← getConstInfo name
    match info with
    | .inductInfo info => specialiseInduct info input
    | .defnInfo info => specialiseDefn info input
    | _ => unreachable!

    trace[nunchaku.mono] m!"Specialising {name} for {input} done"

  specialiseInduct (info : InductiveVal) (input : GroundInput) : SpecializeM Unit := do
    if info.all.length != 1 then
      throwError m!"Can't monomorphise mutual inductives: {info.all}"

    let name := info.name
    let specName := (← get).specialisationCache[(FlowVariable.mk name, input)]!
    let specType ← specialiseConstType info.toConstantVal input
    let newCtors ← info.ctors.mapM (specialiseCtor specName · input)
    trace[nunchaku.mono] m!"Proposing {specType} {newCtors.map (·.type)}"

    let decl := {
      name := specName,
      type := specType,
      ctors := newCtors
    }
    let nparams := info.numParams - (← getMonoArgPositions name).size
    addDecl <| .inductDecl [] nparams [decl] false

  specialisedCtorName (inductSpecName : Name) (ctorName : Name) : SpecializeM Name := do
    let .str _ n := ctorName | throwError m!"Weird ctor name {ctorName}"
    return .str inductSpecName n

  specialiseCtor (inductSpecName : Name) (ctorName : Name) (input : GroundInput) :
      SpecializeM Constructor := do
    let info ← getConstVal ctorName
    let specName ← specialisedCtorName inductSpecName ctorName
    let specType ← specialiseConstType info input
    return ⟨specName, specType⟩

  specialiseDefn (info : DefinitionVal) (input : GroundInput) : SpecializeM Unit := do
    let name := info.name
    let specName := (← get).specialisationCache[(FlowVariable.mk name, input)]!
    let specType ← specialiseConstType info.toConstantVal input

    trace[nunchaku.mono] m!"Proposing {specType}"

    let defn := {
      name := specName,
      levelParams := [],
      type := specType,
      value := ← TransforM.mkSorry specType,
      hints := .opaque,
      safety := .safe
    }
    addDecl <| .defnDecl defn

    let equations ← TransforM.getEquationsFor name
    let newEqs ← equations.mapM (specialiseEquation name · input)
    modify fun s => { s with newEquations := s.newEquations.insert specName newEqs }

  specialiseEquation (name : Name) (eq : Expr) (input : GroundInput) :
      SpecializeM Expr := do
    if input.args.isEmpty then
      specialiseExpr eq {}
    else
      let eq ← metaLevels eq
      let stencil ←
        Meta.forallTelescope eq fun forallArgs body => do
          let some (_, lhs, rhs) := body.eq? | throwError m!"Equation is malformed: {eq}"
          let (fn, args) := lhs.getAppFnArgs
          assert! fn == name
          let positions ← getMonoArgPositions fn
          let specialiseArgs := positions.map (fun pos => forallArgs.findIdx (· == args[pos]!))
          assert! positions.size = input.args.size
          return positions.zip input.args

      let instantiated ← specialiseConstTypeAux eq stencil 0 0
      let final ← instantiateMVars instantiated
      specialiseExpr final {}

end Specialise
end Monomorphization
end Transformation
end Nunchaku
