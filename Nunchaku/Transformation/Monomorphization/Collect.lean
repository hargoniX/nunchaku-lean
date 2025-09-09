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

partial def flowTypeOfExpr (expr : Expr) : CollectM FlowTypeArg := do
    match expr with
    | .fvar fvarId =>
      let some flow := (← read).flowFVars.get? fvarId
        | throwError m!"Can't interpret {expr} as a flow type"
      return flow
    | .const const us =>
      let positions ← getMonoArgPositions const
      if !positions.isEmpty then
        throwError m!"Underapplied constant cannot be used as flow type: {expr}"
      return .const const us #[]
    | .app .. =>
      expr.withApp fun fn args => do
        match fn with
        | .const fn us =>
          if TransforM.isBuiltin fn then
            throwError m!"Can't interpret {expr} as a flow type"
          let monoArgPositions ← getMonoArgPositions fn
          if monoArgPositions.isEmpty then
            return .const fn us #[]
          let last := monoArgPositions[monoArgPositions.size - 1]!
          if args.size ≤ last then
            throwError m!"Can't interpret {expr} as a flow type"
          let flowTypes ← monoArgPositions.mapM (fun idx => flowTypeOfExpr args[idx]!)
          return .const fn us flowTypes
        | _ => throwError m!"Can't interpret {expr} as a flow type"
    | .mdata _ e => flowTypeOfExpr e
    | .proj .. | .lit .. | .sort .. | .bvar .. | .mvar .. | .forallE .. | .letE .. | .lam .. =>
      throwError m!"Can't interpret {expr} as a flow type"

partial def collectExpr (expr : Expr) : CollectM Unit := do
  match expr with
  | .const const .. =>
    if TransforM.isBuiltin const then
      return ()
    let positions ← getMonoArgPositions const
    if !positions.isEmpty then
      throwError m!"Underapplied constant cannot be monomorphised: {expr}"

    match ← getConstInfo const with
    | .ctorInfo ctorInfo =>
      addConstraint ⟨ctorInfo.induct⟩ (.vec #[])
    | .inductInfo .. | .defnInfo .. =>
      addConstraint ⟨const⟩ (.vec #[])
    | .axiomInfo .. | .opaqueInfo .. => return ()
    | .recInfo .. | .quotInfo .. | .thmInfo .. =>
      throwError m!"Cannot monomorphise {expr}"
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
        -- TODO: Maybe we have to collect in the ctors of an inductive type upon encountering an
        -- inductive type or one of its ctors
        match ← getConstInfo fn with
        | .ctorInfo ctorInfo =>
          let induct := ctorInfo.induct
          if (← getMonoArgPositions induct).size != monoArgPositions.size then
            throwError m!"Encountered inductive type with type indices or existentials: {expr}"
          addConstraint ⟨induct⟩ (← FlowInput.ofTypes flowTypes)
        | .inductInfo .. | .defnInfo .. =>
          addConstraint ⟨fn⟩ (← FlowInput.ofTypes flowTypes)
        | .opaqueInfo .. | .axiomInfo .. => return ()
        | .recInfo .. | .quotInfo .. | .thmInfo .. =>
          throwError m!"Cannot monomorphise {expr}"
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
        let value := (← var.getValue?).get!
        collectExpr value
      collectExpr body
  | .mdata _ e => collectExpr e
  | .proj _ _ struct =>
    let structTy ← Meta.inferType struct
    collectExpr structTy
    collectExpr struct
  | .lit .. | .sort .. | .fvar .. | .bvar .. | .mvar .. => return ()

def collectFVar (fvar : FVarId) : CollectM Unit := do
    let type ← fvar.getType
    collectExpr (← instantiateMVars type)

def collectMVar (g : MVarId) : CollectM Unit := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    if decl.isLet then throwError "Let declarations not supported"
    trace[nunchaku.mono] m!"Collecting constraints for {mkFVar decl.fvarId}"
    collectFVar decl.fvarId

  trace[nunchaku.mono] m!"Collecting constraints for goal: {← g.getType}"
  collectExpr (← instantiateMVars (← g.getType))

  let allEquations ← TransforM.getEquations
  for (name, nameEquations) in allEquations do
    for eq in nameEquations do
      trace[nunchaku.mono] m!"Collecting constraints for equation: {eq}"
      Meta.forallTelescope eq fun _ body => do
        let some (_, lhs, rhs) := body.eq? | throwError m!"Equation is malformed: {eq}"
        let (fn, args) := lhs.getAppFnArgs
        assert! fn == name
        let positions ← getMonoArgPositions fn
        let mut flowArgs := #[]
        for pos in positions do
          let arg := args[pos]!
          if !arg.isFVar then
            throwError m!"Equation lhs contains non fvar type argument: {eq}"
          flowArgs := flowArgs.push (arg.fvarId!, .index ⟨name⟩ pos)

        let insertVars flowFVars :=
          flowArgs.foldl (init := flowFVars) (fun acc (fvar, flow) => acc.insert fvar flow)
        withReader (fun (ctx : CollectCtx) => { ctx with flowFVars := insertVars ctx.flowFVars }) do
          -- TODO: this is probably a no-op, args are fvar and we ignore fvar
          args.forM collectExpr
          collectExpr rhs

public partial def collectConstraints (g : MVarId) : MonoAnalysisM (List FlowConstraint) := do
  let mut flowFVars := {}
  let (_, st) ← collectMVar g |>.run { flowFVars } |>.run {}
  return st.constraints.toList

end Collect
end Monomorphization
end Transformation
end Nunchaku
