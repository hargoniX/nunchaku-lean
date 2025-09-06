import Nunchaku.Util.Pipeline
import Nunchaku.Util.Model
import Nunchaku.Util.LocalContext
import Std.Data.Iterators

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
  | const (name : Name) (us : List Level) (args : Array FlowTypeArg)
  deriving Inhabited, BEq, Hashable

private def FlowTypeArg.findTypeVar (type : FlowTypeArg) : Option FlowVariable :=
  match type with
  | .index var .. => some var
  | .const _ _ args => Id.run do
    for arg in args do
      if let some var := findTypeVar arg then
        return some var
    return none

private def FlowTypeArg.findTypeVarIn (types : Array FlowTypeArg) : Option FlowVariable := Id.run do
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
    | .const name us args => m!"{name}.{us} {args.map go}"

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
  | vec (vec : Array FlowTypeArg)
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
  | const (name : Name) (us : List Level) (args : Array GroundTypeArg)
  deriving Inhabited, BEq, Hashable

instance : ToMessageData GroundTypeArg where
  toMessageData := go
where
  go (arg : GroundTypeArg) : MessageData :=
    match arg with
    | .const name us args => m!"{toMessageData name}.{us} {args.map go}"

/--
An assignment to a vector of type variables.
-/
private structure GroundInput where
  args : Array GroundTypeArg
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
  | .const name us args => return .const name us (← args.mapM FlowTypeArg.toGroundTypeArg)
  | .index .. => none

private def FlowInput.toGroundInput (inp : FlowInput) : Option GroundInput := do
  match inp with
  | .var .. => none
  | .vec args =>
    return ⟨← args.mapM FlowTypeArg.toGroundTypeArg⟩

private def GroundTypeArg.toFlowTypeArg (arg : GroundTypeArg) : FlowTypeArg :=
  match arg with
  | .const name us args => .const name us (args.map GroundTypeArg.toFlowTypeArg)

private partial def GroundTypeArg.toExpr (arg : GroundTypeArg) : Expr :=
  match arg with
  | .const name us args => mkAppN (.const name us) (args.map GroundTypeArg.toExpr)

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
      if ← Meta.isType args[idx] then
        positions := positions.push idx

    modifyThe MonoAnalysisState fun s => { s with argPos := s.argPos.insert const positions }

    return positions

private def FlowInput.ofTypes (types : Array FlowTypeArg) : MonoAnalysisM FlowInput := do
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

private partial def collectConstraints (g : MVarId) : MonoAnalysisM (List FlowConstraint) := do
  let mut flowFVars := {}
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
          -- TODO: Maybe we have to collect in the ctors of an inductive type upon encountering an
          -- inductive type or one of its ctors
          match ← getConstInfo fn with
          | .ctorInfo ctorInfo =>
            let induct := ctorInfo.induct
            if (← getMonoArgPositions induct).size != monoArgPositions.size then
              throwError m!"Encountered inductive type with type indices or existentials: {expr}"
            addConstraint ⟨ctorInfo.induct⟩ (← FlowInput.ofTypes flowTypes)
          | .inductInfo .. | .defnInfo .. =>
            addConstraint ⟨fn⟩ (← FlowInput.ofTypes flowTypes)
          | .recInfo .. | .quotInfo .. | .opaqueInfo .. | .axiomInfo .. | .thmInfo .. =>
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
    | .const name us args => .const name us (partiallyInstantiate args fact)
    | .index var idx =>
      if var == fact.dst then
        fact.src.args[idx]! |>.toFlowTypeArg
      else
        .index var idx

  partiallyInstantiate (args : Array FlowTypeArg) (fact : GroundConstraint) : Array FlowTypeArg :=
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

private partial def specialize (g : MVarId) : SpecializeM MVarId := do
  for (const, eqs) in (← TransforM.getEquations) do
    if !(← read).solution.contains ⟨const⟩ then
      trace[nunchaku.mono] m!"Skipping specialisation of {const}"
      modify fun s => { s with newEquations := s.newEquations.insert const eqs }

  trace[nunchaku.mono] m!"Specialising in {g}"
  let g ← mapMVarId g specialiseExpr
  return g
where
  getMonoArgPositions (const : Name) : SpecializeM (Array Nat) := do
    return (← read).analysis.argPos[const]!

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
              specialiseConst info.induct
              let (others, targets) ← partitionMonoArgPositions info.name args
              let pattern : FlowVariable × GroundInput :=
                ⟨⟨info.induct⟩, ⟨← targets.mapM (fun (e, _) => groundTypeOfExpr e)⟩⟩
              let specialisedInductName := (← get).specialisationCache[pattern]!
              let remainingArgs ← others.mapM (specialiseExpr · subst)
              let specialisedName ← specialisedCtorName specialisedInductName info.name
              return mkAppN (.const specialisedName []) remainingArgs
            | .inductInfo info | .defnInfo info =>
              specialiseConst fn
              let (others, targets) ← partitionMonoArgPositions info.name args
              let pattern : FlowVariable × GroundInput :=
                ⟨⟨info.name⟩, ⟨← targets.mapM (fun (e, _) => groundTypeOfExpr e)⟩⟩
              let specialisedName := (← get).specialisationCache[pattern]!
              let remainingArgs ← others.mapM (specialiseExpr · subst)
              return mkAppN (.const specialisedName []) remainingArgs
            | .recInfo .. | .quotInfo .. | .opaqueInfo .. | .axiomInfo .. | .thmInfo .. =>
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
    | .proj _ _ _ => throwError m!"Don't know how to specialise projection {expr}"
    | .fvar .. => return subst.apply expr
    | .const .. | .lit .. | .sort .. | .bvar .. | .mvar .. => return expr

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
    let stencil := positions.zip input.args
    let instantiated ← specialiseConstTypeAux type stencil 0 0
    let final ← instantiateMVars instantiated
    specialiseExpr final {}

  specialiseConst (name : Name) : SpecializeM Unit := do
    let flow := FlowVariable.mk name
    trace[nunchaku.mono] m!"Specialising {name}"
    for input in (← read).solution[flow]! do
      if (← get).specialisationCache.contains (flow, input) then
        continue
      let specName ← mkAuxDeclName name
      modify fun s =>
        { s with specialisationCache := s.specialisationCache.insert (flow, input) specName }
      specialiseConstFor name input
    trace[nunchaku.mono] m!"Specialising {name} done"

  specialiseConstFor (name : Name) (input : GroundInput) : SpecializeM Unit := do
    trace[nunchaku.mono] m!"Specialising {name} for {input}"

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

    let defn := {
      name := specName,
      levelParams := [],
      type := specType,
      value := ← Meta.mkSorry specType false,
      hints := .opaque,
      safety := .safe
    }
    addDecl <| .defnDecl defn

    let equations ← TransforM.getEquationsFor name
    let newEqs ← equations.mapM (specialiseEquation name · input)
    modify fun s => { s with newEquations := s.newEquations.insert specName newEqs }

  specialiseEquation (name : Name) (eq : Expr) (input : GroundInput) :
      SpecializeM Expr :=
    /-
    Equation is of form
    ∀ ..., f args = body

    1. Telescope over args
    2. fetch specialisation positions
    3. based on that identify relevant fvars by inspecting `args`
    4. build substitution from fvars to input and apply
    5. replace all types, constructor calls and recursive function calls recursively with their
       specialised equivalents
    6. re-abstract over non specialised fvars
    -/
    sorry

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
        let (g, st) ← (specialize g).run { analysis := monoAnalysis, solution }
        TransforM.replaceEquations st.newEquations
        trace[nunchaku.mono] m!"Result: {g}"
        return (g, ())
    decode _ res := return res
  }

end Monomorphization
end Transformation
end Nunchaku
