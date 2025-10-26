module

public import Nunchaku.Transformation.Monomorphization.Util

namespace Nunchaku
namespace Transformation
namespace Monomorphization
namespace Collect

open Lean

structure CollectCtx where
  flowFVars : FVarIdMap FlowTypeArg := {}

structure CollectState where
  constraints : Std.HashSet FlowConstraint := {}
  seenExpr : Std.HashSet Expr := {}
  seenConst : Std.HashSet Name := {}

abbrev CollectM := ReaderT CollectCtx <| StateRefT CollectState MonoAnalysisM

def FlowInput.ofTypes (types : Array FlowTypeArg) : MonoAnalysisM FlowInput := do
  if types.isEmpty then
    return .vec #[]
  let firstType := types[0]!
  match firstType with
  | .index flowVar 0 =>
    for shouldIdx in 1...types.size do
      let elem := types[shouldIdx]!
      match elem with
      | .index flowVar' isIdx =>
        if flowVar != flowVar' || isIdx != shouldIdx then
          return .vec types
      | _ => return .vec types

    if types.size == (← getMonoArgPositions flowVar.function).size then
      return .var flowVar
    else
      return .vec types
  | _ => return .vec types

def addConstraint (flowVariable : FlowVariable) (input : FlowInput) : CollectM Unit := do
  if let .var inputVar := input then
    if flowVariable == inputVar then
      -- drop trivial constraints of the form `input ⊑ input`.
      return ()
  let constr := ⟨input, flowVariable⟩
  modify fun s => { s with constraints := s.constraints.insert constr }

def alreadyVisitedExpr (e : Expr) : CollectM Bool := do
  modifyGet fun { constraints, seenExpr, seenConst } =>
    let (fresh, seenExpr) := seenExpr.containsThenInsert e
    (fresh, { constraints, seenExpr, seenConst })

def alreadyVisitedConst (c : Name) : CollectM Bool := do
  modifyGet fun { constraints, seenExpr, seenConst } =>
    let (fresh, seenConst) := seenConst.containsThenInsert c
    (fresh, { constraints, seenExpr, seenConst })

partial def flowTypeOfExpr (expr : Expr) : CollectM FlowTypeArg := do
    match expr with
    | .fvar fvarId =>
      let some flow := (← read).flowFVars.get? fvarId
        | throwError m!"Can't interpret {expr} as a flow type"
      return flow
    | .const const _ =>
      let positions ← getMonoArgPositions const
      if !positions.isEmpty then
        throwError m!"Underapplied constant cannot be used as flow type: {expr}"
      return .const const #[]
    | .app .. =>
      expr.withApp fun fn args => do
        match fn with
        | .const fn _ =>
          if TransforM.isBuiltin fn then
            throwError m!"Can't interpret {expr} as a flow type"
          let monoArgPositions ← getMonoArgPositions fn
          if monoArgPositions.isEmpty then
            return .const fn #[]
          let last := monoArgPositions[monoArgPositions.size - 1]!
          if args.size ≤ last then
            throwError m!"Can't interpret {expr} as a flow type"
          let flowTypes ← monoArgPositions.mapM (fun idx => flowTypeOfExpr args[idx]!)
          return .const fn flowTypes
        | _ => throwError m!"Can't interpret {expr} as a flow type"
    | .mdata _ e => flowTypeOfExpr e
    | .forallE _ dom codom _ =>
      if !expr.isArrow then
        throwError m!"Can't interpret {expr} as a flow type"
      return .func (← flowTypeOfExpr dom) (← flowTypeOfExpr codom)
    | .proj .. | .lit .. | .sort .. | .bvar .. | .mvar .. | .letE .. | .lam .. =>
      throwError m!"Can't interpret {expr} as a flow type"

mutual

partial def collectConstType (info : ConstantVal) : CollectM Unit := do
  Meta.forallTelescope info.type fun args out => do
    let positions ← getMonoArgPositions info.name
    let flowArgs := positions.mapIdx fun posIdx pos =>
      (args[pos]!.fvarId!, .index ⟨info.name⟩ posIdx)
    let insertVars flowFVars :=
      flowArgs.foldl (init := flowFVars) (fun acc (fvar, flow) => acc.insert fvar flow)
    withReader (fun (ctx : CollectCtx) => { ctx with flowFVars := insertVars ctx.flowFVars }) do
      args.forM fun arg => do
        let type ← arg.fvarId!.getType
        collectExpr type
      collectExpr out

partial def collectConst (const : Name) : CollectM Unit := do
  if ← alreadyVisitedConst const then
    return ()
  match ← getConstInfo const with
  | .inductInfo info =>
    collectConstType info.toConstantVal
    let inductPositions ← getMonoArgPositions const
    for ctor in info.ctors do
      -- If we introduce existentials this constraint needs to change
      addConstraint ⟨const⟩ (.var ⟨ctor⟩)
      let info ← getConstVal ctor
      Meta.forallTelescope info.type fun args out => do
        let positions ← getMonoArgPositions ctor
        if positions.size != inductPositions.size then
          throwError m!"Cannot monomorphise existential types in {ctor}"
        -- TODO: consider deduplication with collectConstType
        let flowArgs := positions.mapIdx fun posIdx pos =>
          (args[pos]!.fvarId!, .index ⟨ctor⟩ posIdx)
        let insertVars flowFVars :=
          flowArgs.foldl (init := flowFVars) (fun acc (fvar, flow) => acc.insert fvar flow)
        withReader (fun (ctx : CollectCtx) => { ctx with flowFVars := insertVars ctx.flowFVars }) do
          args.forM fun arg => do
            let type ← arg.fvarId!.getType
            collectExpr type
          collectExpr out
  | .defnInfo info =>
    collectConstType info.toConstantVal
    let positions ← getMonoArgPositions const
    for eq in ← TransforM.getEquationsFor const do
      Meta.forallTelescope eq fun args body => do
        let some (_, lhs, rhs) := body.eq? | throwError m!"Equation is malformed: {eq}"
        let (fn, fnArgs) := lhs.getAppFnArgs
        assert! fn == const
        let flowArgs ← positions.mapIdxM fun posIdx pos => do
          let fnArg := fnArgs[pos]!
          if !fnArg.isFVar then
            throwError m!"Equation lhs contains non fvar type argument: {eq}"
          return (fnArg.fvarId!, .index ⟨const⟩ posIdx)

        let insertVars flowFVars :=
          flowArgs.foldl (init := flowFVars) (fun acc (fvar, flow) => acc.insert fvar flow)
        withReader (fun (ctx : CollectCtx) => { ctx with flowFVars := insertVars ctx.flowFVars }) do
          fnArgs.forM collectExpr
          args.forM fun arg => do
            let type ← arg.fvarId!.getType
            collectExpr type
          collectExpr rhs
  | .axiomInfo info => collectConstType info.toConstantVal
  | .opaqueInfo info => collectConstType info.toConstantVal
  | .ctorInfo info => collectConst info.induct
  | .recInfo .. | .quotInfo .. | .thmInfo .. =>
    throwError m!"Cannot monomorphise {const}"


partial def collectExpr (expr : Expr) : CollectM Unit := do
  if ← alreadyVisitedExpr expr then
    return ()
  match expr with
  | .const const .. =>
    if TransforM.isBuiltin const then
      return ()
    let positions ← getMonoArgPositions const
    if !positions.isEmpty then
      throwError m!"Underapplied constant cannot be monomorphised: {expr}"

    collectConst const
    addConstraint ⟨const⟩ (.vec #[])
  | .app .. =>
    expr.withApp fun fn args => do
      args.forM collectExpr
      match fn.constName? with
      | some fn =>
        if TransforM.isBuiltin fn then
          return ()
        let monoArgPositions ← getMonoArgPositions fn
        if !monoArgPositions.isEmpty then
          let last := monoArgPositions[monoArgPositions.size - 1]!
          if args.size ≤ last then
            throwError m!"Underapplied constant cannot be monomorphised: {expr}"
        let flowTypes ← monoArgPositions.mapM (fun idx => flowTypeOfExpr args[idx]!)
        collectConst fn
        addConstraint ⟨fn⟩ (← FlowInput.ofTypes flowTypes)
      | none => collectExpr fn
  | .lam .. =>
    Meta.lambdaTelescope expr fun vars body => do
      for var in vars do
        if ← Meta.isTypeFormer var then
          throwError m!"Cannot monomorphise generic lambda: {expr}"
        collectExpr (← var.fvarId!.getType)
      collectExpr body
  | .forallE .. =>
    Meta.forallTelescope expr fun vars body => do
      for var in vars do
        let var := var.fvarId!
        let type ← var.getType
        collectExpr type
      collectExpr body
  | .letE .. =>
    Meta.letTelescope expr fun vars body => do
      for var in vars do
        let var := var.fvarId!
        let type ← var.getType
        collectExpr type
        let value := (← var.getValue? (allowNondep := true)).get!
        collectExpr value
      collectExpr body
  | .mdata _ e => collectExpr e
  | .proj _ _ struct =>
    let structTy ← Meta.inferType struct
    collectExpr structTy
    collectExpr struct
  | .lit .. | .sort .. | .fvar .. | .bvar .. | .mvar .. => return ()

end

def collectFVar (fvar : FVarId) : CollectM Unit := do
  let type ← fvar.getType
  collectExpr (← instantiateMVars type)

def collectMVar (g : MVarId) : CollectM Unit := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    trace[nunchaku.mono] m!"Collecting constraints for {mkFVar decl.fvarId}"
    collectFVar decl.fvarId

  trace[nunchaku.mono] m!"Collecting constraints for goal: {← g.getType}"
  collectExpr (← instantiateMVars (← g.getType))

public partial def collectConstraints (g : MVarId) : MonoAnalysisM (List FlowConstraint) := do
  let mut flowFVars := {}
  let (_, st) ← collectMVar g |>.run { flowFVars } |>.run {}
  return st.constraints.toList

end Collect
end Monomorphization
end Transformation
end Nunchaku
