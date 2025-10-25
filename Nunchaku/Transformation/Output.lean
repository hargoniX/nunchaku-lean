module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.NunchakuSyntax
public import Nunchaku.Util.Model
import Nunchaku.Util.NunchakuBuilder
import Nunchaku.Util.NunchakuPrinter
import Nunchaku.Util.AuxiliaryConsts
import Lean.Util.SCC

/-!
This module contains the transformation for turning a monomorphized and dependently typed eliminated
fragment of Lean into Nunchaku logic.
-/

namespace Nunchaku
namespace Transformation
namespace Output

open Lean

inductive LeanIdentifier where
  | goal (g : MVarId)
  | assumption (fvar : FVarId)
  | const (name : Name)
  deriving BEq, Hashable, Repr, Inhabited

structure CollectState where
  dependencies : Std.HashMap LeanIdentifier (List LeanIdentifier) := {}

abbrev CollectM := StateRefT CollectState TransforM

def addDependencies (ident : LeanIdentifier) (deps : List LeanIdentifier) : CollectM Unit :=
  modify fun s => { s with dependencies := s.dependencies.insert ident deps }

partial def constDependencies (name : Name) : TransforM (List Name) := do
  match (← getConstInfo name) with
  | .axiomInfo info | .opaqueInfo info => return Expr.getUsedConstants info.type |>.toList
  | .defnInfo info =>
    let tyConsts := Expr.getUsedConstantsAsSet info.type
    let eqs ← TransforM.getEquationsFor info.name
    let allConsts := eqs.foldl (init := tyConsts) fun acc eq =>
      acc.insertMany eq.getUsedConstants
    return allConsts.toList
  | .inductInfo info =>
    let tyConsts := Expr.getUsedConstantsAsSet info.type
    let allConsts ← info.ctors.foldlM (init := tyConsts) fun acc ctor => do
      let ctor ← getConstInfoCtor ctor
      return acc.insertMany ctor.type.getUsedConstants
    return allConsts.toList
  | .ctorInfo info => constDependencies info.induct
  | .recInfo .. | .thmInfo .. | .quotInfo .. =>
    throwError m!"Cannot figure out dependencies for {name}"

def exprDependencies (expr : Expr) : CollectM (List LeanIdentifier) := do
  let (_, deps) ← expr.forEachWhere (fun e => e.isConst || e.isFVar || e.isProj) collect |>.run {}
  return deps.toList
where
  collect (e : Expr) : StateRefT (Std.HashSet LeanIdentifier) CollectM Unit := do
    match e with
    | .const name .. => modify fun s => s.insert <| .const name
    | .fvar fvar => modify fun s => s.insert <| .assumption fvar
    | .proj structName .. => modify fun s => s.insert <| .const structName
    | _ => return ()

def identDependencies (item : LeanIdentifier) : CollectM (List LeanIdentifier) := do
  match item with
  | .goal g =>
    let type ← g.getType
    exprDependencies type
  | .assumption fvar =>
    let type ← fvar.getType
    exprDependencies type
  | .const name =>
    let deps ← constDependencies name
    return deps.map .const

partial def collectDepGraph (g : MVarId) :
    TransforM (Std.HashMap LeanIdentifier (List LeanIdentifier)) := do
  let mut worklist := [.goal g]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then
      continue
    worklist := .assumption decl.fvarId :: worklist
  let (_, { dependencies, .. }) ← go worklist |>.run {}
  return dependencies
where
  go (worklist : List LeanIdentifier) : CollectM Unit := do
    match worklist with
    | [] => return ()
    | item :: worklist =>
      if (← get).dependencies.contains item then
        go worklist
      else
        let deps ← identDependencies item
        let deps := deps.filter
          fun
            | .const name => !TransforM.isBuiltin name
            | _ => true
        addDependencies item deps
        let newDeps ← deps.filterM fun dep => do
          return !(← get).dependencies.contains dep
        go (newDeps ++ worklist)

structure OutputState where
  commands : Array NunCommand := #[]
  /--
  Counter used for fresh nunchaku variable identifiers.
  -/
  idCounter : Nat := 0
  /--
  Cache for name mangling and later recovery of mangled names.
  -/
  mangleTable : Std.HashMap Lean.Name String := {}
  /--
  Set of mangled projection names.
  -/
  projSet : Std.HashSet String := {}
  /--
  Set of mangled uninterpreted variable names
  -/
  fvarSet : Std.HashSet String := {}


abbrev OutputM := StateRefT OutputState TransforM

def addCommand (cmd : NunCommand) : OutputM Unit := do
  modify fun s => { s with commands := s.commands.push cmd }

def freshNunId : OutputM Nat := do
  modifyGet fun s => (s.idCounter, { s with idCounter := s.idCounter + 1})

def mangleName (name : Lean.Name) : OutputM String := do
  if let some s := (← get).mangleTable[name]? then
    return s

  let comps := name.components.map (fun c => c.toString.replace "_" "__")
  let base := "l_" ++ String.intercalate "_" comps
  let mut out := ""
  for char in base.toList do
    if char.isAlphanum || char == '_' then
      out := out.push char
    else
      let num := char.toNat
      out := out ++ s!"u{num}"
  modify fun s => { s with mangleTable := s.mangleTable.insert name out }
  return out

def mangleFVarName (fvarId : FVarId) : OutputM String := do
  let origName ← fvarId.getUserName
  modify fun s => { s with fvarSet := s.fvarSet.insert origName.toString }
  let mangled ← mangleName (← fvarId.getUserName)
  return mangled

partial def encodeType (expr : Lean.Expr) : OutputM NunType := do
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
        | .const name _ => return .const (← mangleName name) []
        | .fvar id => return .const (← mangleFVarName id) []
        | .forallE .. => go type
        | _ => throwError m!"Don't know how to encode {type} as output type"
      let encodedArgsTypes ← argsTypes.mapM encodeHeadType
      let encodeOutType type := do
        match type.consumeMData with
        | .sort 0 => return .prop
        | .sort (.succ _) => return .type
        | .const name _ => return .const (← mangleName name) []
        | .fvar id => return .const (← mangleFVarName id) []
        | _ => throwError m!"Don't know how to encode {type} as output type"
      let encodedOutType ← encodeOutType output
      return .ofList (encodedArgsTypes.toList ++ [encodedOutType]) (by simp)

def getProjName (struct : Name) (idx : Nat) : OutputM String := do
  let mangled ← mangleName <| Name.str struct s!"proj_{idx}"
  modify fun s => { s with projSet := s.projSet.insert mangled }
  return mangled

partial def encodeTerm (expr : Lean.Expr) : OutputM NunTerm := do
  let expr ← instantiateMVars expr
  go expr {}
where
  go (expr : Lean.Expr) (locals : FVarIdMap Nat) : OutputM NunTerm := do
    match expr with
    | .fvar fvarId =>
      if let some nunId := locals.get? fvarId then
        return .var <| idToVar nunId
      else
        return .const (← mangleFVarName fvarId)
    | .const ``True [] => return .builtin .true
    | .const ``False [] => return .builtin .false
    | .const name _ => return .const (← mangleName name)
    | .app fn arg =>
      match_expr expr with
      | Not p => return .not (← go p locals)
      -- TODO Asserting
      | And lhs rhs => return .and (← go lhs locals) (← go rhs locals)
      | Or lhs rhs => return .or (← go lhs locals) (← go rhs locals)
      | Eq _ lhs rhs => return .eq (← go lhs locals) (← go rhs locals)
      | Ne _ lhs rhs => return .neq (← go lhs locals) (← go rhs locals)
      | Iff lhs rhs => return .equiv (← go lhs locals) (← go rhs locals)
      | classicalIf _ discr lhs rhs  =>
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
            return .exists (idToVar argId) encodedType encodedBody
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
        return .lam (idToVar argId) encodedType encodedBody
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
          return .forall (idToVar argId) encodedType encodedBody
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
        return .let (idToVar argId) encodedValue encodedBody
    | .mdata _ e => go e locals
    | .proj structName idx struct =>
      let projName ← getProjName structName idx
      return .app (.const projName) (← go struct locals)
    | _ => throwError m!"Don't know how to encode term {expr}"
  idToVar (n : Nat) : String := s!"nun_var_{n}"

def arrowN (n : Nat) (type : Expr) : MetaM (Array Expr × Expr) :=
  Meta.forallBoundedTelescope type n fun xs out => do
    unless xs.size = n do
      throwError "type {type} does not have {n} parameters"
    let types ← xs.mapM (Meta.inferType ·)
    for t in types do
      if t.hasAnyFVar (fun fvar => xs.contains (.fvar fvar)) then
        throwError "unexpected dependent type {t} in {type}"
    return (types, out)

def encodePredCtor (ctor : Name) : OutputM NunTerm := do
  let info ← getConstInfoCtor ctor
  /-
  Nunchaku expects our ctors to be of the form
  forall xs, cond => Pred ys
  While in Lean we have two additional freedoms:
  1. Conditions and data can be mixed in the quantifiers
  2. Conditions are separated with → instead of ∧

  Thus the following transformation does two things:
  1. Quantifiers quantify over all values first
  2. Then one large conjunct of all conditions
  3. Then the conclusion
  4. Then call normal type encoder

  Note that this transformation is only generally possible because we have eliminated dependent
  types and should thus have no dependency on proofs in our types.
  -/
  let processed ←
    Meta.forallTelescope info.type fun args concl => do
      let mut values := #[]
      let mut props := #[]
      for arg in args do
        if ← Meta.isProp (← arg.fvarId!.getType) then
          props := props.push arg
        else
          values := values.push arg

      trace[nunchaku] m!"{values}, {props}, {concl}"
      if h : 0 < props.size then
        let cond ← props[1:].foldlM (init := ← props[0].fvarId!.getType) fun acc prop => do
          let prop ← prop.fvarId!.getType
          return mkAnd acc prop
        let body ← mkArrow cond concl
        Meta.mkForallFVars values body
      else
        Meta.mkForallFVars values concl
  encodeTerm processed

def encodeDataCtor (ctor : Name) : OutputM NunCtorSpec := do
  let info ← getConstInfoCtor ctor
  if info.numParams != 0 then
    throwError "Inductive data type should be fully monomorphic at this point"
  let args ← Meta.arrowDomainsN info.numFields info.type
  let encodedArgs ← args.mapM encodeType
  let mangled ← mangleName ctor
  return { name := mangled, arguments := encodedArgs.toList }

def encodeDataType (val : InductiveVal) : OutputM Unit := do
  let mutualTypes := val.all
  let encodedTypes ← mutualTypes.mapM fun typ => do
    let mangled ← mangleName typ
    let val ← getConstInfoInduct typ
    let ctors ← val.ctors.mapM encodeDataCtor
    if val.ctors.isEmpty then
      throwError m!"{val.name} has no constructors"
    return { name := mangled, ctors }

  addCommand <| .dataDecl encodedTypes

  if isStructureLike (← getEnv) val.name then
    assert! val.ctors.length == 1
    let ctor := val.ctors[0]!
    let ctorInfo ← getConstInfoCtor ctor
    Meta.forallTelescope ctorInfo.type fun args out => do
      for idx in 0...args.size do
        let field := args[idx]!
        let lhs := .proj val.name idx (mkAppN (.const ctor []) args)
        let rhs := field
        let eq ← Meta.mkEq lhs rhs
        let law ← Meta.mkForallFVars args eq
        let type ← mkArrow out (← field.fvarId!.getType)
        let encodedLaw ← encodeTerm law
        let encodedType ← encodeType type
        addCommand <| .recDecl
          [{ name := ← getProjName val.name idx, type := encodedType, laws := [encodedLaw] }]

def encodeIndPredicate (val : InductiveVal) : OutputM Unit := do
  let mutualTypes := val.all
  let encodedTypes ← mutualTypes.mapM fun typ => do
    let val ← getConstInfoInduct typ
    let args := val.numParams + val.numIndices
    let (argTypes, outType) ← arrowN args val.type
    if outType != .sort 0 then
      throwError m!"Cannot encode non Prop inductive type with arguments {val.name}"
    -- It's an inductive proposition
    let mangledName ←  mangleName val.name
    let encodedArgTypes ← argTypes.mapM encodeType
    let encodedOutType ← encodeType outType
    let encodedType := .ofList (encodedArgTypes.toList ++ [encodedOutType]) (by simp)

    if val.ctors.isEmpty then
      throwError m!"{val.name} has no constructors"
    let laws ← val.ctors.mapM encodePredCtor
    return { name := mangledName, type := encodedType, laws }

  addCommand <| .predDecl encodedTypes

def encodeDefn (defns : List DefinitionVal) : OutputM Unit := do
  let encodedDefns ← defns.mapM fun defn => do
    let eqns ← TransforM.getEquationsFor defn.name
    if eqns.isEmpty then
      throwError m!"{defn.name} has no equations"
    let encodedEqns ← eqns.mapM encodeTerm
    let encodedType ← encodeType defn.type
    let mangled ← mangleName defn.name
    return { name := mangled, type := encodedType, laws := encodedEqns }

  addCommand <| .recDecl encodedDefns

def encodeInduct (val : InductiveVal) : OutputM Unit := do
  match val.type with
  | .sort (.succ _) =>
    encodeDataType val
  | _ =>
    let args := val.numParams + val.numIndices
    let (_, outType) ← arrowN args val.type
    if outType != .sort 0 then
      throwError m!"Cannot encode non Prop inductive type with arguments {val.name}"

    encodeIndPredicate val

def encodeComponent (component : List LeanIdentifier) : OutputM Unit := do
  match component with
  | [.goal goal] =>
    let statement ← goal.getType
    trace[nunchaku.output] m!"Encoding the goal: {statement}"
    let encoded ← encodeTerm statement
    addCommand <| .goalDecl encoded
  | [.assumption fvar] =>
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
      let mangled ← mangleFVarName fvar
      addCommand <| .valDecl mangled encoded
    | ttype => throwError m!"Don't know how to handle {mkFVar fvar} : {type} : {ttype}"
  | [.const name] =>
    trace[nunchaku.output] m!"Encoding constant: {mkConst name}"
    let constInfo ← getConstInfo name
    match constInfo with
    | .axiomInfo val | .opaqueInfo val =>
      if (← Meta.inferType val.type).isProp then
        let encoded ← encodeTerm val.type
        addCommand <| .axiomDecl encoded
      else
        let encodedType ← encodeType val.type
        let mangled ← mangleName name
        addCommand <| .valDecl mangled encodedType
    | .defnInfo val => encodeDefn [val]
    | .inductInfo val => encodeInduct val
    | .thmInfo val | .ctorInfo val | .recInfo val =>
      trace[nunchaku.output] m!"Ignoring {val.name} as it should be irrelevant"
      return ()
    | .quotInfo _ => throwError "Cannot handle quotients"
  | .const name :: remainder =>
    trace[nunchaku.output] m!"Encoding mutual component with {name}"
    let constInfo ← getConstInfo name
    match constInfo with
    | .defnInfo val =>
      let remainder ← remainder.mapM fun ident => do
        let .const name := ident |
          throwError m!"Non definition in mutual definition block {val.name}"
        getConstInfoDefn name
      let vals := val :: remainder
      encodeDefn vals
    | .inductInfo val =>
      -- inductive types are already organized as SCCs through the `.all` field
      encodeInduct val
    | _ => throwError m!"Cannot handle mutual {name}"
  | _ => unreachable!


def encode (components : List (List LeanIdentifier)) : OutputM Unit := do
  components.forM encodeComponent

structure DecodeCtx where
  decodeTable : Std.HashMap String String
  projSet : Std.HashSet String
  fvarSet : Std.HashSet String

abbrev DecodeM := ReaderT DecodeCtx TransforM

def decodeTypeInhabitant (name : String) : DecodeM String := do
  let some endPos := name.revPosOf '_' | throwError m!"Weird type inhabitant name: {name}"
  let typeName := name.extract ⟨1⟩ endPos
  let typeId := name.extract endPos name.endPos
  let decodedTypeName := (← read).decodeTable[typeName]!
  return s!"${decodedTypeName}{typeId}"

def decodeConstName (name : String) : DecodeM String :=
  if name.startsWith "$" && !name.startsWith "$$" then
    decodeTypeInhabitant name
  else
    return (← read).decodeTable.getD name name

def decodeType (t : NunType) : DecodeM NunType := do
  match t with
  | .prop | .type => return t
  | .const name [] => return .const (← decodeConstName name) []
  | .const _ _ => throwError m!"Expected only monomorphic types in decoding: {t}"
  | .arrow l r => return .arrow (← decodeType l) (← decodeType r)

def decodeTerm (t : NunTerm) : DecodeM NunTerm := do
  match t with
  | .var .. | .builtin .. => return t
  | .const name => return .const (← decodeConstName name)
  | .lam id ty body => return .lam id (← decodeType ty) (← decodeTerm body)
  | .forall id ty body => return .forall id (← decodeType ty) (← decodeTerm body)
  | .exists id ty body => return .exists id (← decodeType ty) (← decodeTerm body)
  | .let id value body => return .let id (← decodeTerm value) (← decodeTerm body)
  | .app fn arg => return .app (← decodeTerm fn) (← decodeTerm arg)

def decode (model : NunModel) : DecodeM NunModel := do
  let decls : List NunModelDecl ← model.decls.filterMapM fun decl => do
    match decl with
    | .type name members =>
      let members ← members.mapM decodeTypeInhabitant
      return some <| .type (← read).decodeTable[name]! members
    | .val name value =>
      if (← read).projSet.contains name then
        -- No need to interpret projections
        return none
      match (← read).decodeTable[name]? with
      | some unmangled =>
        let unmangledName := String.toName unmangled
        if (← getEnv).contains unmangledName then
          -- A global constant, we don't care about nunchaku's interpretation of it
          return none
        else
          -- A local hypothesis, we definitely want to keep it
          return some <| .val unmangled (← decodeTerm value)
      | none =>
        -- An auxiliary declaration, we should keep it
        return some <| .val name (← decodeTerm value)
    | .witness name value => return some <| .witness name (← decodeTerm value)

  -- Now that we've dropped declarations there may be unused auxiliary functions around
  let mut visited : Std.HashSet String := {}
  let mut worklist ← decls.filterM fun
    | .val name _ => return (← read).fvarSet.contains name
    | .type .. | .witness .. => return true
  let decls := Std.HashMap.ofList <| decls.map (fun d => (d.name, d))
  let mut relevant := #[]
  while true do
    let decl :: rest := worklist | break
    worklist := rest
    if visited.contains decl.name then
      continue
    match decl with
    | .type .. => relevant := relevant.push decl
    | .val _ val | .witness _ val =>
      relevant := relevant.push decl
      let used := val.collectUsedConstants |>.toList.filterMap decls.get?
      let used := used.filter (fun d => !visited.contains d.name)
      worklist := worklist ++ used

    visited := visited.insert decl.name

  let decls := relevant.qsort (·.name < ·.name) |>.toList
  return { decls }

public def transformation : Transformation Lean.MVarId NunProblem NunResult NunResult where
  st := DecodeCtx
  inner := {
    name := "Output"
    encode g := g.withContext do
      let dependencies ← collectDepGraph g
      let components := SCC.scc dependencies.keys (dependencies[·]!)
      let (_, { commands, mangleTable, projSet, fvarSet, .. }) ← encode components |>.run {}
      let mut decodeTable := Std.HashMap.emptyWithCapacity mangleTable.size
      for (k, v) in mangleTable do
        if decodeTable.contains v then
          throwError "Non injective name mangling detected, aborting"
        decodeTable := decodeTable.insert v k.toString
      let problem := { commands := commands.toList }
      return (problem, { decodeTable, projSet, fvarSet })
    decode ctx res := do
      ReaderT.run (res.mapM decode) ctx
  }


end Output
end Transformation
end Nunchaku
