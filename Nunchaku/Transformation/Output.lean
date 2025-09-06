import Nunchaku.Util.Pipeline
import Nunchaku.Util.NunchakuSyntax
import Nunchaku.Util.NunchakuBuilder
import Nunchaku.Util.NunchakuPrinter
import Nunchaku.Util.Model

/-!
This module contains the transformation for turning a monomorphized and dependently typed eliminated
fragment of Lean into Nunchaku logic.
-/

namespace Nunchaku
namespace Transformation
namespace Output

open Lean

private inductive LeanIdentifier where
  | goal
  | assumption (fvar : FVarId)
  | const (name : Name)
  deriving BEq, Hashable, Repr, Inhabited

private structure OutputContext where
  /--
  Identifies which part of the Lean context we are currently in to track dependencies
  -/
  currentIdent : LeanIdentifier
  /--
  The goal that we are serializing.
  -/
  goal : MVarId

private structure OutputState where
  /--
  If `id2 ∈ dependencies[id1]` then the commands of `id2` need to come before the ones of `id1`
  in the final Nunchaku problem.
  -/
  dependencies : Std.HashMap LeanIdentifier (List LeanIdentifier) := {}
  /--
  Worklist of remaining identifiers that need to be converted to Nunchaku commands.
  -/
  worklist : List LeanIdentifier
  /--
  Map from identifiers to Nunchaku commands that mirror their effect on the Nunchaku side.
  -/
  commands : Std.HashMap LeanIdentifier (List NunCommand) := {}
  /--
  Set of already visited identifiers in the fixpoint loop.
  -/
  visited : Std.HashSet LeanIdentifier := {}
  /--
  Counter used for fresh nunchaku variable identifiers.
  -/
  idCounter : Nat := 0


private abbrev OutputM := ReaderT OutputContext <| StateRefT OutputState TransforM

private def withCurrentIdent (id : LeanIdentifier) (x : OutputM α) : OutputM α :=
  withReader (fun ctx => { ctx with currentIdent := id }) do
    x

private def getCurrentIdent : OutputM LeanIdentifier := return (← read).currentIdent

private def isVisited (id : LeanIdentifier) : OutputM Bool := return (← get).visited.contains id
private def markVisited (id : LeanIdentifier) : OutputM Unit :=
  modify fun s => { s with
    visited := s.visited.insert id,
    dependencies := s.dependencies.alter id (some <| Option.getD · []),
    commands := s.commands.alter id (some <| Option.getD · []),
  }

private def addCommand (cmd : NunCommand) : OutputM Unit := do
  let id ← getCurrentIdent
  let alter
    | none => some [cmd]
    | some cmds => some (cmd :: cmds)
  modify fun s => { s with commands := s.commands.alter id alter }

private def addCommands (cmds : List NunCommand) : OutputM Unit := do
  let id ← getCurrentIdent
  let alter
    | none => some cmds
    | some curr => some (cmds ++ curr)
  modify fun s => { s with commands := s.commands.alter id alter }

def addDepTo (ident : LeanIdentifier) : OutputM Unit := do
  let currId ← getCurrentIdent
  if currId == ident then
    return
  let alter
    | none => some [ident]
    | some curr => some (ident :: curr)
  modify fun s => { s with dependencies := s.dependencies.alter currId alter }
  if !(← get).visited.contains ident then
    modify fun s => { s with worklist := ident :: s.worklist }

def freshNunId : OutputM Nat := do
  modifyGet fun s => (s.idCounter, { s with idCounter := s.idCounter + 1})

private partial def OutputM.run (idents : List LeanIdentifier) (goal : MVarId) (handle : OutputM Unit) :
    TransforM OutputState := do
  let (_, st) ← StateRefT'.run (ReaderT.run go { currentIdent := .goal, goal }) { worklist := idents }
  return st
where
  go : OutputM Unit := do
    if let ident :: worklist := (← get).worklist then
      modify fun s => { s with worklist }
      if !(← isVisited ident) then
        withCurrentIdent ident do
          handle
        markVisited ident
      go
    else
      return ()

private def mangleName (name : Lean.Name) : String := Id.run do
  let comps := name.components.map (fun c => c.toString.replace "_" "__")
  let base := "l_" ++ String.intercalate "_" comps
  let mut out := ""
  for char in base.toList do
    if char.isAlphanum || char == '_' then
      out := out.push char
    else
      let num := char.toNat
      out := out ++ s!"u{num}"
  return out

private def mangleAssumptionName (fvarId : FVarId) : MetaM String := do
  return mangleName (← fvarId.getUserName)

private partial def encodeType (expr : Lean.Expr) : OutputM NunType := do
  let expr := (← instantiateMVars expr).consumeMData
  go expr
where
  go (expr : Lean.Expr) : OutputM NunType := do
    Meta.forallTelescope expr fun args output => do
      let argsTypes ← args.mapM (Meta.inferType ·)
      if argsTypes.any (fun t => t.hasAnyFVar (fun fvar => args.contains (.fvar fvar))) then
        throwError m!"Cannot encode dependent type {expr}"
      let encodeHeadType type := do
        match type.consumeMData with
        | .sort 0 => return .prop
        | .sort (.succ _) => return .type
        | .const name _ =>
          addDepTo (.const name)
          return .const (mangleName name)
        | .fvar id =>
          addDepTo (.assumption id)
          return .const (← mangleAssumptionName id)
        | .forallE .. => go type
        | _ => throwError m!"Don't know how to encode {type} as output type"
      let encodedArgsTypes ← argsTypes.mapM encodeHeadType
      let encodeOutType type := do
        match type.consumeMData with
        | .sort 0 => return .prop
        | .sort (.succ _) => return .type
        | .const name _ =>
          addDepTo (.const name)
          return .const (mangleName name)
        | .fvar id =>
          addDepTo (.assumption id)
          return .const (← mangleAssumptionName id)
        | _ => throwError m!"Don't know how to encode {type} as output type"
      let encodedOutType ← encodeOutType output
      return .ofList (encodedArgsTypes.toList ++ [encodedOutType]) (by simp)

private partial def encodeTerm (expr : Lean.Expr) : OutputM NunTerm := do
  let expr ← instantiateMVars expr
  go expr {}
where
  go (expr : Lean.Expr) (locals : FVarIdMap Nat) : OutputM NunTerm := do
    match expr with
    | .fvar fvarId =>
      if let some nunId := locals.get? fvarId then
        return .var nunId
      else
        addDepTo (.assumption fvarId)
        return .const (← mangleAssumptionName fvarId)
    | .const ``True [] => return .builtin .true
    | .const ``False [] => return .builtin .false
    | .const name _ =>
      addDepTo (.const name)
      return .const (mangleName name)
    | .app fn arg =>
      match_expr expr with
      | Not p => return .not (← go p locals)
      -- TODO Asserting
      | And lhs rhs => return .and (← go lhs locals) (← go rhs locals)
      | Or lhs rhs => return .or (← go lhs locals) (← go rhs locals)
      | Eq _ lhs rhs => return .eq (← go lhs locals) (← go rhs locals)
      | Ne _ lhs rhs => return .neq (← go lhs locals) (← go rhs locals)
      | Iff lhs rhs => return .equiv (← go lhs locals) (← go rhs locals)
      | ite _ discr _ lhs rhs =>
        return .ite (← go discr locals) (← go lhs locals) (← go rhs locals)
      | Exists ty prop =>
        let encodedType ← encodeType ty
        let argId ← freshNunId
        if prop.isLambda then
          Meta.lambdaBoundedTelescope prop 1 fun arg body => do
            let arg := arg[0]!
            let argType ← Meta.inferType arg
            if argType.hasAnyFVar (fun fvar => locals.contains fvar) then
              throwError m!"Can't encode dependent exists {expr}"
            let locals := locals.insert arg.fvarId! argId
            let encodedBody ← go body locals
            return .exists argId encodedType encodedBody
        else
          -- TODO
          throwError m!"Missing support for lambda free exists {expr}"
      | _ => return .app (← go fn locals) (← go arg locals)
    -- TODO: We can probably make these full telescopes
    | .lam .. =>
      Meta.lambdaBoundedTelescope expr 1 fun arg body => do
        let arg := arg[0]!
        let argType ← Meta.inferType arg
        if argType.hasAnyFVar (fun fvar => locals.contains fvar) then
          throwError m!"Can't encode dependent lambda {expr}"
        let argId ← freshNunId
        let locals := locals.insert arg.fvarId! argId
        let encodedType ← encodeType argType
        let encodedBody ← go body locals
        return .lam argId encodedType encodedBody
    | .forallE _ _ body _ =>
      if (← Meta.inferType expr) != .sort 0 then
        throwError m!"Can't encode forall in non Prop term {expr}"

      -- If it doesn't it must be an implication
      let properForall := body.hasLooseBVars
      Meta.forallBoundedTelescope expr (some 1) fun arg body => do
        let arg := arg[0]!
        let argType ← Meta.inferType arg
        if properForall then
          if argType.hasAnyFVar (fun fvar => locals.contains fvar) then
            throwError m!"Can't encode dependent forall {expr}"
          let argId ← freshNunId
          let locals := locals.insert arg.fvarId! argId
          let encodedType ← encodeType argType
          let encodedBody ← go body locals
          return .forall argId encodedType encodedBody
        else
          let encodedLhs ← go argType locals
          let encodedRhs ← go body locals
          return .imply encodedLhs encodedRhs
    | .letE .. =>
      if !expr.letNondep! then
        throwError m!"Can't encode dependent let {expr}"

      Meta.letBoundedTelescope expr (some 1) fun arg body => do
        let arg := arg[0]!
        let argId ← freshNunId
        let argFVar := arg.fvarId!
        let locals := locals.insert argFVar argId
        let encodedValue ← go ((← argFVar.getValue?).get!) locals
        let encodedBody ← go body locals
        return .let argId encodedValue encodedBody
    | .mdata _ e => go e locals
    -- TODO
    | .proj .. => throwError "Missing support for projections"
    | _ => throwError m!"Don't know how to encode term {expr}"

private def arrowN (n : Nat) (type : Expr) : MetaM (Array Expr × Expr) :=
  Meta.forallBoundedTelescope type n fun xs out => do
    unless xs.size = n do
      throwError "type {type} does not have {n} parameters"
    let types ← xs.mapM (Meta.inferType ·)
    for t in types do
      if t.hasAnyFVar (fun fvar => xs.contains (.fvar fvar)) then
        throwError "unexpected dependent type {t} in {type}"
    return (types, out)


private def encodePredCtor (ctor : Name) : OutputM NunTerm := do
  let info ← getConstInfoCtor ctor
  encodeTerm info.type

private def encodeDataCtor (ctor : Name) : OutputM NunCtorSpec := do
  let info ← getConstInfoCtor ctor
  if info.numParams != 0 then
    throwError "Inductive data type should be fully monomorphic at this point"
  let args ← Meta.arrowDomainsN info.numFields info.type
  let encodedArgs ← args.mapM encodeType
  let mangled := mangleName ctor
  return { name := mangled, arguments := encodedArgs.toList }

/--
Transfers all dependencies of `orig` to `new` and makes `orig` depend on `new` only.
-/
private def transferDeps (orig : LeanIdentifier) (new : LeanIdentifier) : OutputM Unit := do
  let origDeps := (← get).dependencies.getD orig []

  let alterOrig := fun _ => some [new]
  modify fun s => { s with dependencies := s.dependencies.alter orig alterOrig }

  let alterNew := fun currDeps => some (origDeps ++ currDeps.getD [])
  modify fun s => { s with dependencies := s.dependencies.alter new alterNew }

private def encodeDataType (val : InductiveVal) : OutputM Unit := do
  let mutualTypes := val.all
  let rootType ← getCurrentIdent
  let encodedTypes ← mutualTypes.mapM fun typ => do
    let thisType := .const typ
    let cmd ←
      withCurrentIdent thisType do
        let mangled := mangleName typ
        let val ← getConstInfoInduct typ
        let ctors ← val.ctors.mapM encodeDataCtor
        return { name := mangled, ctors }

    if typ != val.name then
      markVisited thisType
      transferDeps thisType rootType

    return cmd

  let filter := Std.HashSet.ofList <| val.all.map LeanIdentifier.const
  let alterRoot :=
    fun
      | none => some []
      | some deps => some <| deps.filter (!filter.contains ·)
  modify fun s => { s with dependencies := s.dependencies.alter rootType alterRoot }
  addCommand <| .dataDecl encodedTypes

private def encodeIndPredicate (val : InductiveVal) : OutputM Unit := do
  let mutualTypes := val.all
  let rootType ← getCurrentIdent
  let encodedTypes ← mutualTypes.mapM fun typ => do
    let thisType := .const typ
    let cmd ←
      withCurrentIdent thisType do
        let val ← getConstInfoInduct typ
        let args := val.numParams + val.numIndices
        let (argTypes, outType) ← arrowN args val.type
        if outType != .sort 0 then
          throwError m!"Cannot encode non Prop inductive type with arguments {val.name}"
        -- It's an inductive proposition
        let mangledName := mangleName val.name
        let encodedArgTypes ← argTypes.mapM encodeType
        let encodedOutType ← encodeType outType
        let encodedType := .ofList (encodedArgTypes.toList ++ [encodedOutType]) (by simp)
        let laws ← val.ctors.mapM encodePredCtor
        return { name := mangledName, type := encodedType, laws }

    if typ != val.name then
      markVisited thisType
      transferDeps thisType rootType

    return cmd

  let filter := Std.HashSet.ofList <| val.all.map LeanIdentifier.const
  let alterRoot :=
    fun
      | none => some []
      | some deps => some <| deps.filter (!filter.contains ·)
  modify fun s => { s with dependencies := s.dependencies.alter rootType alterRoot }
  addCommand <| .predDecl encodedTypes

private def LeanIdentifier.encode : OutputM Unit := do
  match (← getCurrentIdent) with
  | .goal =>
    let statement ← (← read).goal.getType
    trace[nunchaku.output] m!"Encoding the goal: {statement}"
    let encoded ← encodeTerm statement
    addCommand <| .goalDecl encoded
  | .assumption fvar =>
    trace[nunchaku.output] m!"Encoding fvar: {mkFVar fvar}"
    let type ← fvar.getType
    match ← Meta.inferType type with
    | .sort 0 =>
      -- `fvar` is a propositional assumption, we can interpret this as an axiom
      let encoded ← encodeTerm type
      addCommand <| .axiomDecl encoded
    | .sort (.succ _) =>
      -- `fvar` is some uninterpreted proper value, interpet it as such
      let encoded ← encodeType type
      let mangled := mangleName (← fvar.getUserName)
      addCommand <| .valDecl mangled encoded
    | ttype => throwError m!"Don't know how to handle {mkFVar fvar} : {type} : {ttype}"
  | .const name =>
    trace[nunchaku.output] m!"Encoding constant: {mkConst name}"
    let constInfo ← getConstInfo name
    match constInfo with
    | .axiomInfo val =>
      if (← Meta.inferType val.type).isProp then
        let encoded ← encodeTerm val.type
        addCommand <| .axiomDecl encoded
      else
        let encodedType ← encodeType val.type
        let mangled := mangleName name
        addCommand <| .valDecl mangled encodedType
    | .opaqueInfo val =>
      if (← Meta.inferType val.type).isProp then
        let encoded ← encodeTerm val.type
        addCommand <| .axiomDecl encoded
      else
        let encodedType ← encodeType val.type
        let mangled := mangleName name
        addCommand <| .valDecl mangled encodedType
    | .defnInfo val =>
      -- TODO: support for mutual recursion
      let eqns ← TransforM.getEquationsFor name
      let encodedEqns ← eqns.mapM encodeTerm
      let encodedType ← encodeType val.type
      let mangled := mangleName name
      addCommand <| .recDecl [{ name := mangled, type := encodedType, laws := encodedEqns }]
    | .inductInfo val =>
      match val.type with
      | .sort (.succ _) =>
        encodeDataType val
      | _ =>
        let args := val.numParams + val.numIndices
        let (_, outType) ← arrowN args val.type
        if outType != .sort 0 then
          throwError m!"Cannot encode non Prop inductive type with arguments {name}"

        encodeIndPredicate val
    | .thmInfo val | .ctorInfo val | .recInfo val =>
      trace[nunchaku.output] m!"Ignoring {val.name} as it should be irrelevant"
      return ()
    | .quotInfo _ => throwError "Cannot handle quotients"

private structure TopoContext where
  deps : Std.HashMap LeanIdentifier (List LeanIdentifier)
  cmds : Std.HashMap LeanIdentifier (List NunCommand)

private abbrev TopoM :=
  ReaderT TopoContext <| StateT (Std.HashMap LeanIdentifier Bool) <| Except String

private partial def OutputState.toProblem (state : OutputState) : Except String NunProblem :=
  let deps := state.dependencies
  let cmds := state.commands
  let worklist := state.dependencies.keys
  go worklist (Array.emptyWithCapacity cmds.size) |>.run { deps, cmds } |>.run' {}
where
  go (worklist : List LeanIdentifier) (acc : Array NunCommand) : TopoM NunProblem := do
    match worklist with
    | [] =>
      let acc := acc ++ (← read).cmds[LeanIdentifier.goal]!
      return { commands := acc.toList }
    | elem :: worklist =>
      let acc ← visit elem acc
      go worklist acc

  visit (elem : LeanIdentifier) (acc : Array NunCommand) : TopoM (Array NunCommand) := do
    if elem == .goal then
      return acc

    if let some mark := (← get)[elem]? then
      match mark with
      | true => return acc
      | false => throw "Graph has a cycle"

    modify fun s => s.insert elem false

    let mut acc := acc
    for predecessor in (← read).deps[elem]! do
      acc ← visit predecessor acc

    modify fun s => s.insert elem true
    return acc ++ (← read).cmds[elem]!

def transformation : Transformation Lean.MVarId NunProblem NunResult LeanResult where
  st := Unit
  inner := {
    name := "Output"
    encode g := g.withContext do
      let mut idents := [.goal]
      for decl in ← getLCtx do
        if decl.isImplementationDetail then
          continue
        if decl.isLet then throwError "Let declarations not supported"
        idents := .assumption decl.fvarId :: idents
      let state ← OutputM.run idents g LeanIdentifier.encode
      let problem ← IO.ofExcept state.toProblem
      return (problem, ())
    decode _ res := do
      match res with
      | .unsat => return .unsat
      | .unknown => return .unknown
      -- TODO: proper model recovery
      | .sat _ => return .sat []
  }


end Output
end Transformation
end Nunchaku
