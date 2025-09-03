import Nunchaku.Util.Pipeline
import Nunchaku.Util.Model

/-!
This module contains the monomorphisation transformation, it is based on
["The Simple Essence of Monomorphization"](https://se.cs.uni-tuebingen.de/publications/lutze25simple.pdf)
though restricted to the simplest possible fragment in Lean for now.
-/

namespace Nunchaku
namespace Transformation
namespace Monomorphization

open Lean

private structure FlowVariable where
  function : Name
  deriving Inhabited, BEq, Hashable

instance : ToString FlowVariable where
  toString var := Name.toString var.function

/--
A non ground type argument.
-/
private inductive FlowTypeArg where
  /--
  Projecting a particular type out of a flow variable.
  -/
  | index (var : FlowVariable) (idx : Nat)
  /--
  A (potentially polymorphic) type with arguments.
  -/
  | const (name : Name) (args : List FlowTypeArg)
  /--
  An uninterpreted type.
  -/
  | uninterpreted (fvar : FVarId)
  deriving Inhabited, BEq, Hashable

private def FlowTypeArg.findTypeVar (type : FlowTypeArg) : Option FlowVariable :=
  match type with
  | .index var .. => some var
  | .const _ args => Id.run do
    for arg in args do
      if let some var := findTypeVar arg then
        return some var
    return none
  | .uninterpreted .. => none

private def FlowTypeArg.findTypeVarIn (types : List FlowTypeArg) : Option FlowVariable := Id.run do
  for type in types do
    if let some var := findTypeVar type then
      return some var
  return none

instance : ToMessageData FlowTypeArg where
  toMessageData := go
where
  go (ty : FlowTypeArg) : MessageData :=
    match ty with
    | .index var idx => m!"{var}_({idx})"
    | .const name args => m!"{name} {args.map go}"
    | .uninterpreted fvar => m!"{mkFVar fvar}"

/--
The inputs into a flow variable.
-/
private inductive FlowInput where
  /--
  If we want to state that `var` is a subset of whatever it flows into.
  -/
  | var (var : FlowVariable)
  /--
  If we want to state what flow into individual components of our flow variable.
  -/
  | vec (vec : List FlowTypeArg)
  deriving Inhabited, BEq, Hashable

instance : ToMessageData FlowInput where
  toMessageData
    | .var var => toMessageData var
    | .vec vec => toMessageData vec

/--
`input ⊑ var`, recall that `FlowVariable` are vector valued to account for
functions with multiple type arguments and as such `FlowInput` represents a vector of inputs as
well.
-/
private structure FlowConstraint where
  src : FlowInput
  dst : FlowVariable
  deriving Inhabited, BEq, Hashable

instance : ToMessageData FlowConstraint where
  toMessageData constr := m!"{toMessageData constr.src} ⊑ {toMessageData constr.dst}"

/--
A ground type argument.
-/
private inductive GroundTypeArg where
  /--
  A list of ground type arguments applied to a constant are ground.
  -/
  | const (name : Name) (args : List GroundTypeArg)
  /--
  Some monomorphic free variable from the context is ground.
  -/
  | uninterpreted (fvar : FVarId)
  deriving Inhabited, BEq, Hashable

instance : ToMessageData GroundTypeArg where
  toMessageData := go
where
  go (arg : GroundTypeArg) : MessageData :=
    match arg with
    | .const name args => m!"{toMessageData name} {args.map go}"
    | .uninterpreted fvar => m!"{mkFVar fvar}"

/--
An assignment to a vector of type variables.
-/
private structure GroundInput where
  args : List GroundTypeArg
  deriving Inhabited, BEq, Hashable

instance : ToMessageData GroundInput where
  toMessageData i := toMessageData i.args

/--
The type arguments of `dst` are instantiated using the ground type arguments in `src`.
-/
private structure GroundConstraint where
  src : GroundInput
  dst : FlowVariable
  deriving Inhabited, BEq, Hashable

private def FlowTypeArg.toGroundTypeArg (type : FlowTypeArg) : Option GroundTypeArg := do
  match type with
  | .const name args => return .const name (← args.mapM FlowTypeArg.toGroundTypeArg)
  | .index .. => none
  | .uninterpreted fvar => return .uninterpreted fvar

private def FlowInput.toGroundInput (inp : FlowInput) : Option GroundInput := do
  match inp with
  | .var .. => none
  | .vec args =>
    return ⟨← args.mapM FlowTypeArg.toGroundTypeArg⟩

private def GroundTypeArg.toFlowTypeArg (arg : GroundTypeArg) : FlowTypeArg :=
  match arg with
  | .const name args => .const name (args.map GroundTypeArg.toFlowTypeArg)
  | .uninterpreted fvar => .uninterpreted fvar

structure MonoAnalysisState where
  /--
  Which of the arguments of a function `f` are type arguments that we consider for monomorphisation.
  -/
  argPos : Std.HashMap Name (Array Nat) := {}

private abbrev MonoAnalysisM := StateRefT MonoAnalysisState TransforM

private def MonoAnalysisM.run (x : MonoAnalysisM α) : TransforM (α × MonoAnalysisState) :=
  StateRefT'.run x {}

structure CollectCtx where
  flowFVars : FVarIdMap FlowTypeArg := {}

structure CollectState where
  constraints : Std.HashSet FlowConstraint := {}

private abbrev CollectM := ReaderT CollectCtx <| StateRefT CollectState MonoAnalysisM

private def getMonoArgPositions (const : Name) : MonoAnalysisM (Array Nat) := do
  if let some cached := (← getThe MonoAnalysisState).argPos[const]? then
    return cached

  let ty := (← getConstVal const).type
  Meta.forallTelescope ty fun args _ => do
    let mut positions := #[]
    for h : idx in 0...args.size do
      if ← Meta.isTypeFormer args[idx] then
        positions := positions.push idx

    modifyThe MonoAnalysisState fun s => { s with argPos := s.argPos.insert const positions }

    return positions

private def FlowInput.ofTypes (types : List FlowTypeArg) : MonoAnalysisM FlowInput := do
  let firstType := types[0]!
  match firstType with
  | .index flowVar 0 =>
    let mut shouldIdx := 1
    for elem in types.tail do
      match elem with
      | .index flowVar' isIdx =>
        if flowVar != flowVar' || isIdx != shouldIdx then
          return .vec types
      | _ => return .vec types
      shouldIdx := shouldIdx + 1
    if shouldIdx == (← getMonoArgPositions flowVar.function).size then
      return .var flowVar
    else
      return .vec types
  | _ => return .vec types

private partial def collectConstraints (g : MVarId) : MonoAnalysisM (List FlowConstraint) := do
  let mut flowFVars := {}
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    if decl.isLet then throwError "Let declarations not supported"
    -- TODO: if the fvar takes a type former argument itself we have to throw an error
    let fvar := decl.fvarId
    if ← Meta.isTypeFormer (mkFVar fvar) then
      flowFVars := flowFVars.insert fvar (.uninterpreted fvar)
  let (_, st) ← go g |>.run { flowFVars } |>.run {}
  return st.constraints.toList
where
  go (g : MVarId) : CollectM Unit := do
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
            args.forM collectExpr
            collectExpr rhs

  collectFVar (fvar : FVarId) : CollectM Unit := do
    let type ← fvar.getType
    collectExpr (← instantiateMVars type)

  addConstraint (flowVariable : FlowVariable) (input : FlowInput) : CollectM Unit := do
    if let .var inputVar := input then
      if flowVariable == inputVar then
        -- drop trivial constraints of the form `input ⊑ input`.
        return ()
    let constr := ⟨input, flowVariable⟩
    modify fun s => { s with constraints := s.constraints.insert constr }

  flowTypeOfExpr (expr : Expr) : CollectM FlowTypeArg := do
    let expr ← Meta.whnfR expr
    match expr with
    | .fvar fvarId =>
      let some flow := (← read).flowFVars.get? fvarId
        | throwError m!"Can't interpret {expr} as a flow type"
      return flow
    | .const const .. =>
      let positions ← getMonoArgPositions const
      if !positions.isEmpty then
        throwError m!"Underapplied constant cannot be used as flow type: {expr}"
      return .const const []
    | .app .. =>
      expr.withApp fun fn args => do
        match fn.constName? with
        | some fn =>
          if TransforM.isBuiltin fn then
            throwError m!"Can't interpret {expr} as a flow type"
          let monoArgPositions ← getMonoArgPositions fn
          if monoArgPositions.isEmpty then
            return .const fn []
          let last := monoArgPositions[monoArgPositions.size - 1]!
          if args.size ≤ last then
            throwError m!"Can't interpret {expr} as a flow type"
          let flowTypes ← monoArgPositions.mapM (fun idx => flowTypeOfExpr args[idx]!)
          return .const fn flowTypes.toList
        | none => throwError m!"Can't interpret {expr} as a flow type"
    | .mdata _ e => flowTypeOfExpr e
    | .proj .. | .lit .. | .sort .. | .bvar .. | .mvar .. | .forallE .. | .letE .. | .lam .. =>
      throwError m!"Can't interpret {expr} as a flow type"

  collectExpr (expr : Expr) : CollectM Unit := do
    match expr with
    | .const const .. =>
      if TransforM.isBuiltin const then
        return ()
      let positions ← getMonoArgPositions const
      if !positions.isEmpty then
        throwError m!"Underapplied constant cannot be monomorphised: {expr}"
    | .app .. =>
      expr.withApp fun fn args => do
        args.forM collectExpr
        match fn.constName? with
        | some fn =>
          if TransforM.isBuiltin fn then
            return ()
          let monoArgPositions ← getMonoArgPositions fn
          if monoArgPositions.isEmpty then
            return ()
          let last := monoArgPositions[monoArgPositions.size - 1]!
          if args.size ≤ last then
            throwError m!"Underapplied constant cannot be monomorphised: {expr}"
          let flowTypes ← monoArgPositions.mapM (fun idx => flowTypeOfExpr args[idx]!)
          match ← getConstInfo fn with
          | .ctorInfo ctorInfo =>
            let induct := ctorInfo.induct
            if (← getMonoArgPositions induct).size != monoArgPositions.size then
              throwError m!"Encountered inductive type with type indices or existentials: {expr}"
            addConstraint ⟨ctorInfo.induct⟩ (← FlowInput.ofTypes flowTypes.toList)
          | .inductInfo .. | .defnInfo .. | .thmInfo .. | .axiomInfo .. =>
            addConstraint ⟨fn⟩ (← FlowInput.ofTypes flowTypes.toList)
          | .recInfo .. | .quotInfo .. | .opaqueInfo ..  =>
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
      -- TODO: Maybe we have to collect in the inferred type of `struct`?
      collectExpr struct
    | .lit .. | .sort .. | .fvar .. | .bvar .. | .mvar .. => return ()

private def constraintsSolvable (constraints : List FlowConstraint) : Bool :=
  -- TODO
  true

private structure SolveCtx where
  /--
  The (non-ground) rules that we need to apply until a fixpoint is reached.
  -/
  rules : Array FlowConstraint

private structure SolveState where
  /--
  Whether the last iteration of the fixpoint solver caused a change.
  -/
  changed : Bool := false
  /--
  Ground facts that we have so far collected about the constraint system.
  -/
  facts : Std.HashSet GroundConstraint
  /--
  An accumulator for new facts in this iteration of the fixpoint solver.
  -/
  newFacts : List GroundConstraint := []

private abbrev SolveM := ReaderT SolveCtx <| StateM SolveState

private partial def solveConstraints (constraints : List FlowConstraint)
    (_h : constraintsSolvable constraints) :
    Std.HashMap FlowVariable (List GroundInput) := Id.run do
  let mut facts := {}
  let mut rules := #[]
  for constraint in constraints do
    match constraint.src.toGroundInput with
    | some ground => facts := facts.insert ⟨ground, constraint.dst⟩
    | none => rules := rules.push constraint
  let (_, st) := go |>.run { rules } |>.run { facts }
  let mut solution := {}
  for fact in st.facts do
    solution :=
      solution.alter fact.dst fun
        | some stuff => fact.src :: stuff
        | none => [fact.src]
  return solution
where
  go : SolveM Unit := do
    modify fun s => { s with changed := false }
    step
    if (← get).changed then
      go
    else
      return ()

  step : SolveM Unit := do
    for rule in (← read).rules do
      workRule rule
    commitNewFacts

  partiallyInstantiateFlowType (arg : FlowTypeArg) (fact : GroundConstraint) : FlowTypeArg :=
    match arg with
    | .uninterpreted fvar => .uninterpreted fvar
    | .const name args => .const name (partiallyInstantiate args fact)
    | .index var idx =>
      if var == fact.dst then
        fact.src.args[idx]! |>.toFlowTypeArg
      else
        .index var idx

  partiallyInstantiate (args : List FlowTypeArg) (fact : GroundConstraint) : List FlowTypeArg :=
    args.map (partiallyInstantiateFlowType · fact)

  workRule (rule : FlowConstraint) : SolveM Unit := do
    match rule.src with
    | .vec args =>
      match FlowTypeArg.findTypeVarIn args with
      | some tvar =>
        -- the rule is not ground, instantiate one argument and repeat until grounded
        -- TODO: index facts
        for fact in (← get).facts do
          if fact.dst == tvar then
            let newArgs := partiallyInstantiate args fact
            let newRule := { rule with src := .vec newArgs }
            workRule newRule
      | none =>
        -- The rule is already ground
        learnFact { src := rule.src.toGroundInput.get! , dst := rule.dst  }
    | .var inputVar =>
      -- we have inputVar ⊑ rule.dst and find fact.src ⊑ inputVar
      -- -> need to forward fact.src into rule.dst
      -- TODO: index facts
      for fact in (← get).facts do
        if fact.dst == inputVar then
          learnFact { fact with dst := rule.dst }

  @[inline]
  learnFact (fact : GroundConstraint) : SolveM Unit := do
    modify fun s => { s with newFacts := fact :: s.newFacts }

  commitNewFacts : SolveM Unit := do
    for fact in (← get).newFacts do
      modify fun { facts, changed, newFacts } =>
        let (contains, facts) := facts.containsThenInsert fact
        { facts := facts, changed := changed || !contains, newFacts }
    modify fun s => { s with newFacts := [] }

structure SpecializeContext where
  analysis : MonoAnalysisState
  solution : Std.HashMap FlowVariable (List GroundInput)

structure SpecializeState where
  newEquations : Std.HashMap Name (List Expr) := {}
  specialisationCache : Std.HashMap (FlowVariable × GroundInput) Name := {}

private abbrev SpecializeM := ReaderT SpecializeContext <| StateRefT SpecializeState TransforM

private def SpecializeM.run (x : SpecializeM α) (ctx : SpecializeContext) :
    TransforM (α × SpecializeState) :=
  StateRefT'.run (ReaderT.run x ctx) {}

private def generateSpecialisations : SpecializeM Unit := sorry

private def applySpecialisations (g : MVarId) : SpecializeM MVarId := sorry

private def specialize (g : MVarId) : SpecializeM MVarId := sorry

def transformation : Transformation MVarId MVarId LeanResult LeanResult where
  st := Unit
  inner := {
    name := "Monomorphisation"
    encode g := g.withContext do
      let (constraints, monoAnalysis) ← (collectConstraints g).run
      if h : !constraintsSolvable constraints then
        throwError "The goal cannot be monomorphised."
      else
        trace[nunchaku.mono] m!"Constraints: {constraints}"
        let solution := solveConstraints constraints (by simpa using h)
        trace[nunchaku.mono] m!"Solution: {solution.toList}"
        --let (g, st) ← (specialize g).run { analysis := monoAnalysis, solution }
        --TransforM.replaceEquations st.newEquations
        return (g, ())
    decode _ res := return res
  }

end Monomorphization
end Transformation
end Nunchaku
