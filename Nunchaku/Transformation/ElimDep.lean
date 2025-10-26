module
public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model
import Nunchaku.Util.LocalContext
import Nunchaku.Util.AddDecls
import Lean.Meta.CollectFVars
import Nunchaku.Util.Decode
import Nunchaku.Util.AuxiliaryConsts
import Lean.Meta.Match.MatchEqsExt

namespace Nunchaku
namespace Transformation
namespace ElimDep

open Lean

/--
The different relevant groups of expressions for us.
-/
inductive ExprKind where
  /--
  The expression is a proof, i.e. `e : τ : Prop`
  -/
  | proof
  /--
  The experssion is a prop, i.e. `e : Prop`
  -/
  | prop
  /--
  Some other expression, e.g. `e : Type` or `e : Data`
  -/
  | other
  deriving Inhabited, Repr, DecidableEq

/--
The different relevant groups of arguments to functions, inductives etc.
-/
inductive ArgKind where
  /--
  The argument is none of the other kinds
  -/
  | value
  /--
  The argument is a proof, i.e. `e : τ : Prop`.
  -/
  | proof
  /--
  The argument is a prop or prop former, i.e. `e : τ1 → ... → Prop`
  -/
  | prop
  /--
  The argument is a type, i.e. `e : Type u`
  -/
  | type
  /--
  The argument is a type former, i.e. `e : τ1 → ... → Type u`
  -/
  | typeformer
  deriving Inhabited, Repr, DecidableEq

namespace ArgKind

def isValue (k : ArgKind) : Bool := k matches .value
def isProof (k : ArgKind) : Bool := k matches .proof
def isProp (k : ArgKind) : Bool := k matches .prop
def isType (k : ArgKind) : Bool := k matches .type

def isInductiveErasable (k : ArgKind) : Bool :=
  k.isProof || k.isValue || k.isProp

end ArgKind

structure DepState where
  /--
  Cache for saving the argument kinds of a particular constant.
  -/
  argCache : Std.HashMap Name (Array ArgKind) := {}
  /--
  Translation cache for constants.
  -/
  constCache : Std.HashMap Name Name := {}
  /--
  Collection of new equations for the new constants
  -/
  newEquations : Std.HashMap Name (List Expr) := {}
  /--
  Cache for saving the characteristic invariants of particular constants
  -/
  invCache : Std.HashMap Name Name := {}
  /--
  Cache for saving the kind of visited expressions in case we see them again.
  -/
  exprKindCache : Std.HashMap Expr ExprKind := {}
  /--
  Cache for saving the encoded version of an expression, additionally indexed by whether we are in a
  `Prop` or non `Prop` context.
  -/
  elimCache : Std.HashMap (Expr × Bool) Expr := {}
  /--
  Cache for matchers specialised to some particular motive
  -/
  matcherCache : Std.HashMap (Name × Expr) Expr := {}
  /--
  PUnit defines a type which has a universe argument that is not determined through type parameters.
  This is fundamentally at odds with our monomorphisation pass. While more types like this exist we
  decided to just special case PUnit for now by creating concrete unit-like-types for each of them
  until a more complete solution is found.
  -/
  unitCache : Std.HashMap Nat Name := {}

abbrev DepM := StateRefT DepState TransforM

structure DecodeCtx where
  decodeTable : Std.HashMap String String
  unitSet : Std.HashSet String

def DepM.run (x : DepM α) : TransforM (α × DecodeCtx) := do
  let (p, { constCache := table, unitCache, newEquations, .. }) ← StateRefT'.run x {}
  TransforM.replaceEquations newEquations
  TransforM.addDecls
  let mut decodeTable := Std.HashMap.emptyWithCapacity table.size
  for (k, v) in table do
    let v := v.toString
    if decodeTable.contains v then
        throwError "Non injective elimdep name mangling detected"
    decodeTable := decodeTable.insert v k.toString
  let unitSet := Std.HashSet.ofList <| unitCache.values.map Name.toString
  return (p, { decodeTable, unitSet })

def getKind (e : Expr) : DepM ExprKind := do
  match (← get).exprKindCache[e]? with
  | some k => return k
  | none =>
    if ← Meta.isProof e then
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .proof }
      return .proof
    else if ← Meta.isProp e then
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .prop }
      return .prop
    else
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .other }
      return .other

def isProof (e : Expr) : DepM Bool := do
  return (← getKind e) == .proof

def isProp (e : Expr) : DepM Bool := do
  return (← getKind e) == .prop

def isNonPropTypeFormer (expr : Expr) : MetaM Bool := do
  let some level ← Meta.typeFormerTypeLevel expr | return false
  return level != 0

/--
We say an expression is a type alias if it is:
- a non propositional type former
- its body contains a lambda with a body of:
  - a constant
  - an application of a constant
  - one of its arguments
  - an arrow type
  - a sort
-/
def isTypeAlias (const : Name) : MetaM Bool := do
  let .defnInfo info ← getConstInfo const | return false
  if !(← isNonPropTypeFormer info.type) then return false
  Meta.lambdaTelescope info.value fun _ body => do
    let body := body.consumeMData
    match body with
    | .fvar .. | .forallE .. | .sort .. => return true
    | .const name .. => return (← isNonPropTypeFormer (← getConstVal name).type)
    | .proj .. => return false
    | .app .. => return body.getAppFn.isConst
    | .mdata .. | .lit .. | .mvar .. | .letE .. | .lam .. | .bvar .. => unreachable!

/--
Recursively unfold all type aliases in `e`
-/
def unfoldTypeAliases (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := pre)
where
  pre (expr : Expr) : MetaM TransformStep := do
    let .const name _ := expr.getAppFn | return .continue
    if ! (← isTypeAlias name) then return .continue
    let some expr ← Meta.unfoldDefinition? expr (ignoreTransparency := true)
      | throwError m!"Failed to unfold type alias {expr}"
    return .visit expr

/--
Given some constants compute a stencil of argument kinds of its type.
-/
def argStencil (info : ConstantVal) : DepM (Array ArgKind) := do
  if let some stencil := (← get).argCache[info.name]? then
    return stencil

  let stencil ← Meta.forallTelescope info.type fun args _ => do
    let mut drop := #[]
    for idx in 0...args.size do
      let arg := args[idx]!
      let argType ← Meta.inferType arg
      let argType ← unfoldTypeAliases argType
      if ← isProof arg then
        drop := drop.push .proof
      else if ← Meta.isPropFormerType argType then
        drop := drop.push .prop
      else if argType.isType then
        drop := drop.push .type
      else if ← Meta.isTypeFormerType argType then
        drop := drop.push .typeformer
      else
        drop := drop.push .value

    return drop

  modify fun s => { s with argCache := s.argCache.insert info.name stencil }
  return stencil

-- TODO: dedup with specialise
def elimCtorName (inductElimName : Name) (ctorName : Name) : MetaM Name := do
  let .str _ n := ctorName | throwError m!"Weird ctor name {ctorName}"
  return .str inductElimName n

/--
Correct a projection index of a structure by accounting for the fact that proofs were dropped from
it.
-/
def correctProjIndex (typeName : Name) (idx : Nat) : DepM Nat := do
  let inductInfo ← getConstInfoInduct typeName
  let ctorName := inductInfo.ctors[0]!
  let inductStencil ← argStencil inductInfo.toConstantVal
  let ctorStencil ← argStencil (← getConstVal ctorName)
  let ctorStencil := ctorStencil.drop inductStencil.size
  let slice := ctorStencil[0...idx].toArray
  let newIdx := idx - slice.countP ArgKind.isProof
  trace[nunchaku.elimdep] m!"Adjusting projection on {typeName} from {idx} to {newIdx}"
  return newIdx

def maxLit : Nat := 2^16

@[inline]
partial def elimExtendForall' [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (args : Array Expr) (body : Expr) (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (extender : Expr → Meta.FVarSubst → FVarId → m (Option Expr))
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr)
    (subst : Meta.FVarSubst := {}) : m Expr := do
  go args body 0 #[] #[] subst
where
  @[specialize]
  go (args : Array Expr) (body : Expr) (idx : Nat) (allFVars : Array Expr)
      (changedFVars : Array Expr) (subst : Meta.FVarSubst) : m Expr := do
    if h : idx < args.size then
      let arg := args[idx]
      if ← dropArg idx arg then
        go args body (idx + 1) allFVars changedFVars subst
      else
        let fvar := arg.fvarId!
        let origType ← fvar.getType
        let newType ← argHandler origType subst
        Meta.withLocalDecl (← fvar.getUserName) (← fvar.getBinderInfo) newType fun newArg => do
          let subst := subst.insert fvar newArg
          let allFVars := allFVars.push newArg
          let changedFVars := changedFVars.push newArg
          if let some additional ← extender origType subst newArg.fvarId! then
            Meta.withLocalDecl `h .default additional fun additionalArg => do
            let allFVars := allFVars.push additionalArg
            go args body (idx + 1) allFVars changedFVars subst
          else
            go args body (idx + 1) allFVars changedFVars subst
    else
      let newBody ← bodyHandler body subst changedFVars
      let newExpr ← Meta.mkForallFVars allFVars newBody
      return newExpr

@[inline]
partial def elimExtendForall [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (expr : Expr) (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (extender : Expr → Meta.FVarSubst → FVarId → m (Option Expr))
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr)
    (subst : Meta.FVarSubst := {}) : m Expr := do
  Meta.forallTelescope expr fun args body => do
    elimExtendForall' args body dropArg argHandler extender bodyHandler subst

@[inline]
partial def elimForall' [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (args : Array Expr) (body : Expr)
    (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr) (subst : Meta.FVarSubst := {}) :
    m Expr := do
  elimExtendForall' args body dropArg argHandler (fun _ _ _ => return none) bodyHandler subst

@[inline]
partial def elimForall [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (expr : Expr) (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr)
    (subst : Meta.FVarSubst := {}) : m Expr := do
  Meta.forallTelescope expr fun args body => do
    elimForall' args body dropArg argHandler bodyHandler subst

structure IndInvState where
  props : Std.HashMap FVarId FVarId := {}

/--
A monad for tracking the free variables of predicates that are associated with type arguments.
-/
abbrev IndInvM := ReaderT IndInvState DepM

namespace IndInvM

def run (x : IndInvM α) : DepM α :=
  ReaderT.run x {}

@[inline]
def withPropFor (var : FVarId) (prop : FVarId) (x : IndInvM α) : IndInvM α :=
  withReader (fun s => { s with props := s.props.insert var prop }) do
    x

def getPropFor? (var : FVarId) : IndInvM (Option FVarId) :=
  return (← read).props[var]?

end IndInvM

@[inline]
def withEnrichedArgs (args : Array Expr) (body : Expr)
    (inductStencil : Array ArgKind) (k : Array (Expr × Bool) → Expr → IndInvM α) : IndInvM α := do
  go #[] 0 args body inductStencil k
where
  @[specialize]
  go (acc : Array (Expr × Bool)) (idx : Nat) (args : Array Expr) (body : Expr)
      (inductStencil : Array ArgKind) (k : Array (Expr × Bool) → Expr → IndInvM α) : IndInvM α := do
    if h : idx < args.size then
      let arg := args[idx]
      let acc := acc.push (arg, true)
      if idx < inductStencil.size && inductStencil[idx]!.isType then
        Meta.withLocalDeclD `h (← mkArrow arg (.sort 0)) fun propArg => do
          let acc := acc.push (propArg, false)
          IndInvM.withPropFor arg.fvarId! propArg.fvarId! do
            go acc (idx + 1) args body inductStencil k
      else
        go acc (idx + 1) args body inductStencil k
    else
      k acc body

def enrichStencil (stencil : Array ArgKind) : Array ArgKind := Id.run do
  let mut new := Array.emptyWithCapacity stencil.size
  for arg in stencil do
    new := new.push arg
    if arg.isType then
      new := new.push .prop
  return new

partial def mkAuxiliaryMatcher (fn : Name) (motive : Expr) (info : Meta.MatcherInfo) :
    IndInvM Expr := do
  match (← get).matcherCache[(fn, motive)]? with
  | some fn => return fn
  | none =>
    let expr ← Meta.mkConstWithFreshMVarLevels fn
    let type ← Meta.inferType expr
    let specialisedType ← Meta.forallBoundedTelescope type (some info.numParams) fun args body => do
      let .forallE _ type body _ := body | unreachable!
      let typeLevel ← Meta.getLevel type
      let motiveLevel ← Meta.getLevel (← Meta.inferType motive)
      if !(← Meta.isLevelDefEq typeLevel motiveLevel) then
        throwError m!"Failed to instantiate motive argument {motive} for {type}"
      let body := body.instantiate1 motive
      -- In case we are dealing with just a lambda that drops the first argument
      let body ← Core.betaReduce body
      Meta.mkForallFVars args body
    let u ← Meta.getLevel specialisedType
    let elimName ← TransforM.mkFreshName fn (pref := "match_elim_")
    let newFn ← Meta.mkAuxDefinition (compile := false)
      elimName
      specialisedType
      (TransforM.mkSorryAx specialisedType u)
    let eqns := (← Meta.Match.getEquationsFor fn).eqnNames
    let newEqns ← eqns.mapM (transformEquation · fn newFn)
    trace[nunchaku.elimdep] m!"Created auxiliary matcher: {newFn}, eqns: {newEqns}"
    TransforM.injectEquations elimName newEqns.toList
    modify fun s => { s with matcherCache := s.matcherCache.insert (fn, motive) newFn }
    return newFn
where
  transformEquation (eqn : Name) (origName : Name) (elimExpr : Expr) : IndInvM Expr := do
    let expr ← Meta.mkConstWithFreshMVarLevels eqn
    let eq ← Meta.inferType expr
    Meta.forallBoundedTelescope eq (some info.numParams) fun args body => do
      let .forallE _ type body _ := body | unreachable!
      let typeLevel ← Meta.getLevel type
      let motiveLevel ← Meta.getLevel (← Meta.inferType motive)
      if !(← Meta.isLevelDefEq typeLevel motiveLevel) then
        throwError m!"Failed to instantiate motive argument {motive} for {type}"
      let body := body.instantiate1 motive
      -- In case we are dealing with just a lambda that drops the first argument
      let body ← Core.betaReduce body
      let body ← Core.transform body (pre := fun expr => do
        expr.withApp fun fn args => do
          if fn.isConstOf origName then
            let args := args.eraseIdx! info.numParams
            return .visit (mkAppN elimExpr args)
          else
            return .continue
      )
      let body ← Meta.mkForallFVars elimExpr.getAppArgs body
      Meta.mkForallFVars args body

def auxiliaryUnitCtor : Name := `unit

def mkAuxiliaryUnitType (lvl : Level) : IndInvM Name := do
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

def mkAuxiliaryUnitValue (lvl : Level) : IndInvM Name := do
  let type ← mkAuxiliaryUnitType lvl
  return type ++ auxiliaryUnitCtor

partial def preEliminateConst (const : Name) (us : List Level) :
    IndInvM (Option (Name × List Level)) := do
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

partial def preEliminateApp (fn : Name) (us : List Level) (args : Array Expr) :
    IndInvM (Option Expr) := do
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
  | _ => return none

def argIsCtorIrrelevant (ctorStencil : Array ArgKind) (inductInfo : InductiveVal) (idx : Nat) :
    IndInvM Bool := do
  if idx < inductInfo.numParams then
    let inductStencil ← argStencil inductInfo.toConstantVal
    return inductStencil[idx]!.isInductiveErasable
  else
    return ctorStencil[idx]!.isProof

def filterCtorArgs (ctorStencil : Array ArgKind) (inductInfo : InductiveVal) (xs : Array α) :
    IndInvM (Array α) := do
  let mut new := #[]
  for h : idx in 0...xs.size do
    if !(← argIsCtorIrrelevant ctorStencil inductInfo idx) then
      let arg := xs[idx]
      new := new.push arg
  return new

mutual

/--
Invariant: Never called on proofs
-/
partial def elimValueOrProp' (expr : Expr) (subst : Meta.FVarSubst) : IndInvM Expr := do
  -- TODO: remove debug
  if ← isProof expr then
    throwError m!"Called on proof: {expr}"

  if ← isProp expr then
    elimProp' expr subst
  else
    elimValue' expr subst

partial def elimExpr' (expr : Expr) (inProp : Bool) (subst : Meta.FVarSubst) : IndInvM Expr := do
  if let some cached := (← get).elimCache[(expr, inProp)]? then
    return cached
  else
    let finishedExpr ← elimExprRaw' expr inProp subst
    modify fun s => { s with elimCache := s.elimCache.insert (expr, inProp) finishedExpr }
    return finishedExpr

partial def elimExprRaw' (expr : Expr) (inProp : Bool) (subst : Meta.FVarSubst) : IndInvM Expr := do
  trace[nunchaku.elimdep] m!"elimExpr': {expr}, prop?: {inProp}"
  if inProp && !(← isProp expr) then
    throwError m!"Called on non prop: {expr}"

  if !inProp && (← isProof expr <||> isProp expr) then
    throwError m!"Called on proof or prop: {expr}"

  match expr with
  | .const const us =>
    if TransforM.isBuiltin const then
      return .const const us
    else
      match ← preEliminateConst const us with
      | some (name, lvl) => elimExpr' (.const name lvl) inProp subst
      | none =>
        let const ← elimConst const
        return .const const us
  | .app .. =>
    expr.withApp fun fn args => do
      match fn with
      | .const fn us =>
        match ← preEliminateApp fn us args with
        | some expr => elimExpr' expr inProp subst
        | none =>
          if TransforM.isBuiltin fn then
            let args ← args.mapM (elimValueOrProp' · subst)
            return mkAppN (.const fn us) args
          else if let some info ← Meta.getMatcherInfo? fn then
            -- In the following we assume matches are always just fully applied
            let motive := args[info.numParams]!
            let fn ← mkAuxiliaryMatcher fn motive info
            let args := args.eraseIdx! info.numParams |>.map Option.some
            elimExprRaw' (← Meta.mkAppOptM' fn args) inProp subst
          else
            let defaultBehavior fn args := do
              let fn ← elimConst fn
              let args ← args.filterMapM (elimValuePropNoProof · subst)
              return mkAppN (.const fn us) args

            match ← getConstInfo fn with
            | .inductInfo info =>
              let fn ← elimConst fn
              let stencil ← argStencil info.toConstantVal
              let mut newArgs := #[]
              if ← Meta.isPropFormerType info.type then
                for idx in 0...args.size do
                  match stencil[idx]! with
                  | .proof => continue
                  | .value | .prop =>
                    let arg := args[idx]!
                    newArgs := newArgs.push (← elimValueOrProp' arg subst)
                  | .typeformer | .type =>
                    let arg := args[idx]!
                    newArgs := newArgs.push (← elimValue' arg subst)
                    newArgs := newArgs.push (← invariantPredForD arg subst)
              else
                for idx in 0...args.size do
                  match stencil[idx]! with
                  | .proof | .value | .prop => continue
                  | _ =>
                    let arg := args[idx]!
                    newArgs := newArgs.push (← elimValueOrProp' arg subst)
              return mkAppN (.const fn us) newArgs
            | .ctorInfo info =>
              let .str inductName _ := fn | throwError m!"Weird ctor name {fn}"
              let stencil ← argStencil info.toConstantVal
              let inductInfo ← getConstInfoInduct inductName
              let fn ← elimConst fn
              let args ← filterCtorArgs stencil inductInfo args
              let args ← args.mapM (elimValueOrProp' · subst)
              return mkAppN (.const fn us) args
            | .defnInfo .. =>
              if let some { fromClass := true, ..} ← getProjectionFnInfo? fn then
                /-
                This optimization acts in situations such as `a < b` when `a` and `b`'s types are
                known and then reduces it to the underlying function from the TC instance.
                -/
                let newExpr ← Meta.whnfI expr
                if newExpr != expr then
                  elimExprRaw' newExpr inProp subst
                else
                  defaultBehavior fn args
              else
                defaultBehavior fn args
            | _ => defaultBehavior fn args
      | _ =>
        let fn ← elimValue' fn subst
        let args ← args.filterMapM (elimValuePropNoProof · subst)
        return mkAppN fn args
  | .lam .. =>
    Meta.lambdaBoundedTelescope expr 1 fun args body => do
      let arg := args[0]!
      if ← isProof arg then
        elimValueOrProp' body subst
      else
        let fvarId := arg.fvarId!
        let name ← fvarId.getUserName
        let bi ← fvarId.getBinderInfo
        let newType ← elimValue' (← fvarId.getType) subst

        Meta.withLocalDecl name bi newType fun replacedArg => do
          let newBody ← elimValueOrProp' body (subst.insert fvarId replacedArg)
          Meta.mkLambdaFVars #[replacedArg] newBody
  | .forallE .. =>
    Meta.forallBoundedTelescope expr (some 1) fun args body => do
      let arg := args[0]!
      if ← pure !inProp <&&> isProof arg then
        elimValue' body subst
      else
        let fvarId := arg.fvarId!
        let name ← fvarId.getUserName
        let bi ← fvarId.getBinderInfo
        let oldType ← fvarId.getType
        let newType ← elimValueOrProp' oldType subst

        Meta.withLocalDecl name bi newType fun replacedArg => do
          let subst := subst.insert fvarId replacedArg
          let newBody ← elimExpr' body inProp subst
          if inProp then
            match ← invariantForFVar oldType subst replacedArg.fvarId! with
            | some invariantType =>
              Meta.withLocalDecl `h .default invariantType fun invariantArg => do
                Meta.mkForallFVars #[replacedArg, invariantArg] newBody
            | none =>
              Meta.mkForallFVars #[replacedArg] newBody
          else
            Meta.mkForallFVars #[replacedArg] newBody
  | .letE (nondep := nondep) .. =>
    Meta.letBoundedTelescope expr (some 1) fun args body => do
      let arg := args[0]!
      if ← isProof arg then
        elimExpr' body inProp subst
      else
        let fvarId := arg.fvarId!
        let name ← fvarId.getUserName
        let newType ← elimValue' (← fvarId.getType) subst
        let newValue ← elimValueOrProp' (← fvarId.getValue? (allowNondep := true)).get! subst

        Meta.withLetDecl name newType newValue (nondep := nondep) fun replacedArg => do
          let newBody ← elimExpr' body inProp (subst.insert fvarId replacedArg)
          Meta.mkLetFVars (generalizeNondepLet := false) #[replacedArg] newBody
  | .mdata _ e => elimExpr' e inProp subst
  | .proj typeName idx struct =>
    let struct ← elimValue' struct subst
    let idx ← correctProjIndex typeName idx
    let typeName ← elimConst typeName
    return .proj typeName idx struct
  | .fvar .. => return subst.apply expr
  | .lit (.natVal n) =>
      if n > maxLit then
        throwError m!"Nat literal too large for unary encoding {n}"
      let zero ← elimConst ``Nat.zero
      let succ ← elimConst ``Nat.succ
      let rec aux (n : Nat) (zero succ : Name) (acc : Expr) : Expr :=
        match n with
        | 0 => acc
        | n + 1 => aux n zero succ (mkApp (mkConst succ) acc)
      return aux n zero succ (mkConst zero)
  | .lit (.strVal _) => throwError "String literals unsupported"
  | .sort .. | .bvar .. | .mvar .. => return expr

/--
Invariant: Only called on `Prop`
-/
partial def elimProp' (expr : Expr) (subst : Meta.FVarSubst) : IndInvM Expr := do
  elimExpr' expr true subst

partial def elimValuePropNoProof (expr : Expr) (subst : Meta.FVarSubst) : IndInvM (Option Expr) := do
  if ← isProof expr then
    return none
  else
    return some (← elimValueOrProp' expr subst)

/--
Invariant: Never called on a proof or proposition.
-/
partial def elimValue' (expr : Expr) (subst : Meta.FVarSubst) : IndInvM Expr := do
  elimExpr' expr false subst

partial def elimValueOrProp (expr : Expr) (subst : Meta.FVarSubst) : IndInvM Expr := do
  let expr ← unfoldTypeAliases expr
  elimValueOrProp' expr subst

partial def elimValue (expr : Expr) (subst : Meta.FVarSubst) : IndInvM Expr := do
  let expr ← unfoldTypeAliases expr
  elimValue' expr subst

partial def elimProp (expr : Expr) (subst : Meta.FVarSubst) : IndInvM Expr := do
  let expr ← unfoldTypeAliases expr
  elimProp' expr subst

partial def elimDataConstType (expr : Expr) (stencil : Array ArgKind) : DepM Expr := do
  -- Don't introduce predicates for data constant types
  IndInvM.run <|
    elimForall expr
      (fun idx _ => return stencil[idx]!.isProof)
      elimValue
      (fun b s _ => elimValue b s)

partial def elimPropCtor (inductElimName : Name) (inductStencil : Array ArgKind)
    (ctorName : Name) : DepM Constructor := do
  let info ← getConstVal ctorName
  let elimName ← elimCtorName inductElimName ctorName
  let elimType ← IndInvM.run <|
    Meta.forallTelescope info.type fun args body => do
      let ctorStencil ← argStencil info
      withEnrichedArgs args body ctorStencil fun args body =>
        let args := args.map Prod.fst
        elimExtendForall' args body
          (fun _ _ => return false)
          elimValueOrProp
          invariantForFVar
          fun body subst _ => do
            body.withApp fun origInduct args => do
              let .const _ us := origInduct | throwError m!"Weird ctor: {ctorName}"
              let mut freshArgs := #[]
              for idx in 0...args.size do
                if inductStencil[idx]!.isProof then
                  continue
                let arg ← elimValue args[idx]! subst
                freshArgs := freshArgs.push arg
                if inductStencil[idx]!.isType then
                  let .fvar fvar := args[idx]! |
                    throwError "Encountered type index in {ctorName}"
                  let some prop := ← IndInvM.getPropFor? fvar |
                    throwError "Encountered type argument without invariant in {ctorName}"
                  freshArgs := freshArgs.push (← elimValue (.fvar prop) subst)
              return mkAppN (.const inductElimName us) freshArgs

  modify fun s => { s with constCache := s.constCache.insert ctorName elimName }
  return ⟨elimName, elimType⟩

partial def elimPropInduct (info : InductiveVal) (elimName : Name) (stencil : Array ArgKind) :
    DepM (InductiveType × Nat) := do
  let enrichedStencil := enrichStencil stencil
  let newType ← IndInvM.run <|
    Meta.forallTelescope info.type fun args body =>
      withEnrichedArgs args body stencil fun args body => do
        let args := args.map Prod.fst
        elimForall' args body
          (fun idx _ => return enrichedStencil[idx]!.isProof)
          elimValue
          (fun b s _ => elimValue b s)
  /-
  We set `nparams` to `0` because of inductives that takes generic types.
  In these situations we will inject the generic premises of the shape
  `α → Prop` right when binding `{α : Type}` because the next binder might
  already refer to `α` in some way or form and might thus have to be restricted.
  -/
  let nparams := 0
  let newCtors ← info.ctors.mapM (elimPropCtor elimName stencil)

  let decl := {
    name := elimName,
    type := newType,
    ctors := newCtors
  }
  return (decl, nparams)

partial def elimValueCtor (inductElimName : Name) (inductInfo : InductiveVal)
    (inductStencil : Array ArgKind) (ctorName : Name) : DepM Constructor := do
  let info ← getConstVal ctorName
  let elimName ← elimCtorName inductElimName ctorName
  let stencil ← argStencil info
  let elimType ← IndInvM.run <|
    elimForall info.type
      (fun idx _ => argIsCtorIrrelevant stencil inductInfo idx)
      elimValue
      fun body subst _ =>
        body.withApp fun origInduct args => do
          let .const _ us := origInduct | throwError m!"Weird ctor: {ctorName}"
          let mut freshArgs := #[]
          for idx in 0...args.size do
            if inductStencil[idx]!.isInductiveErasable then
              continue
            let arg ← elimValue args[idx]! subst
            freshArgs := freshArgs.push arg
          return mkAppN (.const inductElimName us) freshArgs

  modify fun s => { s with constCache := s.constCache.insert ctorName elimName }
  return ⟨elimName, elimType⟩

partial def elimValueInduct (info : InductiveVal) (elimName : Name) (stencil : Array ArgKind) :
    DepM (InductiveType × Nat) := do
  let newType ← IndInvM.run <|
    elimForall info.type
      (fun idx _ => return stencil[idx]!.isInductiveErasable)
      elimValue
      (fun b s _ => elimValue b s)

  let nparams :=
    info.numParams - stencil[0...info.numParams].toArray.countP ArgKind.isInductiveErasable

  let newCtors ← info.ctors.mapM (elimValueCtor elimName info stencil)

  let decl := {
    name := elimName,
    type := newType,
    ctors := newCtors
  }

  return (decl, nparams)

partial def elimInduct (info : InductiveVal) : DepM Unit := do
  let name := info.name
  let elimName := (← get).constCache[name]!
  let stencil ← argStencil info.toConstantVal
  let (decl, nparams) ←
    if ← Meta.isPropFormerType info.type then
      elimPropInduct info elimName stencil
    else
      elimValueInduct info elimName stencil

  trace[nunchaku.elimdep] m!"Proposing {decl.type} {decl.ctors.map (·.type)}"
  TransforM.recordDecl <| .inductDecl info.levelParams nparams [decl] false

partial def elimEquation (eq : Expr) : DepM Expr := do
  trace[nunchaku.elimdep] m!"Working eq {eq}"
  Meta.forallTelescope eq fun args body => do
    let (_, { fvarSet, .. }) ← body.collectFVars |>.run {}
    let shouldDrop := fun _ arg => do
      if ← isProof arg then
        return fvarSet.contains arg.fvarId!
      else
        return false
    let res ← IndInvM.run <| elimForall' args body shouldDrop elimValueOrProp (fun b s _ => elimProp b s)
    trace[nunchaku.elimdep] m!"New equation: {res}"
    return res

partial def elimDefn (info : DefinitionVal) : DepM Unit := do
  let name := info.name
  let elimName := (← get).constCache[name]!
  if ← isProp info.type then
    throwError m!"Proofs should be erased but tried to work: {info.name}"

  let stencil ← argStencil info.toConstantVal
  let u ← Meta.getLevel info.type
  let newType ← elimDataConstType info.type stencil
  trace[nunchaku.elimdep] m!"New type for {info.name}: {newType}"

  let decl := {
    name := elimName,
    levelParams := info.levelParams,
    type := newType,
    value := TransforM.mkSorryAx newType u,
    safety := .safe,
    hints := .opaque,
  }

  TransforM.recordDecl <| .defnDecl decl
  let equations ← TransforM.getEquationsFor name
  let newEqs := ← equations.mapM elimEquation
  modify fun s => { s with newEquations := s.newEquations.insert elimName newEqs }

partial def elimAxiomOpaque (info : ConstantVal) : DepM Unit := do
  let name := info.name
  let elimName := (← get).constCache[name]!
  if ← isProp info.type then
    throwError m!"Proofs should be erased but tried to work: {info.name}"

  let stencil ← argStencil info
  let newType ← elimDataConstType info.type stencil
  trace[nunchaku.elimdep] m!"New type for {info.name}: {newType}"

  let decl := {
    name := elimName,
    levelParams := info.levelParams,
    type := newType,
    isUnsafe := false
  }

  TransforM.recordDecl <| .axiomDecl decl

partial def elimTheorem (info : TheoremVal) : DepM Unit := do
  throwError m!"Proofs should be erased but tried to work: {info.name}"

partial def elimConst (name : Name) : DepM Name := do
  if let some name := (← get).constCache[name]? then
    return name
  else
    let info ← getConstInfo name
    if !info.isCtor then
      let elimName ← TransforM.mkFreshName name (pref := "elim_")
      modify fun s => { s with constCache := s.constCache.insert name elimName }

    trace[nunchaku.elimdep] m!"Working {name}"

    match info with
    | .inductInfo info => elimInduct info
    | .defnInfo info => elimDefn info
    | .ctorInfo info => elimInduct (← getConstInfoInduct info.induct)
    | .opaqueInfo info | .axiomInfo info => elimAxiomOpaque info.toConstantVal
    | .thmInfo info => elimTheorem info
    | .recInfo .. | .quotInfo .. =>
      throwError m!"Cannot elim dependent types in {name}"

    trace[nunchaku.elimdep] m!"Done working {name}"
    return (← get).constCache[name]!

partial def ctorToInvariant (inductInvName : Name) (inductInfo : InductiveVal)
    (inductStencil : Array ArgKind) (ctorName : Name) : DepM Constructor := do
  let info ← getConstVal ctorName
  let ctorStencil ← argStencil info
  let elimName ← elimCtorName inductInvName ctorName
  let elimType ← IndInvM.run <|
    Meta.forallTelescope info.type fun args body => do
      withEnrichedArgs args body inductStencil fun args body =>
        let syntheticMask := args.map Prod.snd
        let args := args.map Prod.fst
        let handleBody body subst changedFVars := do
          let lparams := info.levelParams.map .param
          let args ← body.withApp fun _ args => do
            let mut newArgs := #[]
            for idx in 0...args.size do
              let arg := args[idx]!
              match inductStencil[idx]! with
              | .proof => continue
              | .type =>
                newArgs := newArgs.push (← elimValueOrProp' arg subst)
                let some fvarId := arg.fvarId? |
                  throwError m!"Type indices unsupported: {info.name}"
                let some prop ← IndInvM.getPropFor? fvarId |
                  throwError m!"Couldn't find proposition for type variable, likely existential"
                let prop := subst.apply (mkFVar prop)
                newArgs := newArgs.push prop
              | .prop | .typeformer | .value =>
                newArgs := newArgs.push (← elimValueOrProp' arg subst)
            return newArgs
          let elimCtorName ← elimConst ctorName
          let argCandidates := changedFVars.zip syntheticMask |>.filter Prod.snd |>.map Prod.fst
          let ctorArgs ← filterCtorArgs ctorStencil inductInfo argCandidates
          let args := args.push (mkAppN (mkConst elimCtorName lparams) ctorArgs)
          return mkAppN (mkConst inductInvName lparams) args

        elimExtendForall'
          args
          body
          (fun _ _ => return false)
          elimValueOrProp
          invariantForFVar
          handleBody
  return ⟨elimName, elimType⟩

partial def invariantForInduct (info : InductiveVal) : DepM Name := do
  let name := info.name
  if let some name := (← get).invCache[name]? then
    return name

  let invName ← TransforM.mkFreshName name (pref := "inv_")
  modify fun s => { s with invCache := s.invCache.insert name invName }
  let unfoldedType ← unfoldTypeAliases info.type
  let invType ← IndInvM.run <|
    Meta.forallTelescope unfoldedType fun args _ => do
      let valueTy ← Meta.mkAppM name args
      Meta.withLocalDecl `ind .default valueTy fun arg =>
        let args := args.push arg
        elimExtendForall' args (.sort 0)
          (fun _ arg => isProof arg)
          elimValue
          (fun argType _ newArg => do
            if !argType.isType then
              return none
            mkArrow (mkFVar newArg) (.sort 0)
          )
          (fun e _ _ => return e)

  let stencil ← argStencil info.toConstantVal

  let invCtors := ← info.ctors.mapM (ctorToInvariant invName info stencil)
  let decl := {
    name := invName,
    type := invType,
    ctors := invCtors,
  }
  trace[nunchaku.elimdep] m!"Proposing inv {invType} {invCtors.map (·.type)}"

  /-
  See note about nparams on the generic prop inductive eliminator.
  -/
  let nparams := 0
  TransforM.recordDecl <| .inductDecl info.levelParams nparams [decl] false
  return invName

partial def invariantPredForD (oldType : Expr) (subst : Meta.FVarSubst) :
    IndInvM Expr := do
  if let some pred ← invariantPredFor oldType subst then
    return pred
  else
    let elim ← elimValueOrProp' oldType subst
    return mkLambda `x .default elim (mkConst ``True)

partial def invariantForFVar (oldType : Expr) (subst : Meta.FVarSubst) (newFVar : FVarId) :
    IndInvM (Option Expr) := do
  let some inv ← invariantFor oldType subst (mkFVar newFVar) | return none
  Core.betaReduce inv

partial def invariantPredFor (oldType : Expr) (subst : Meta.FVarSubst) :
    IndInvM (Option Expr) := do
  if ← isProp oldType then
    return none
  let oldType ← Meta.zetaReduce oldType
  let oldType ← Core.betaReduce oldType
  let oldType ← unfoldTypeAliases oldType
  let oldType := oldType.consumeMData
  match oldType with
  | .const .. | .app .. =>
    oldType.withApp fun fn args => do
      let .const fn us := fn | return none
      let (fn, us) := (← preEliminateConst fn us).getD (fn, us)
      let .inductInfo info ← getConstInfo fn | return none
      let inductStencil ← argStencil info.toConstantVal
      let invInduct ← invariantForInduct info
      let mut newArgs := #[]
      for idx in 0...args.size do
        let arg := args[idx]!
        match inductStencil[idx]!with
        | .proof => continue
        | .type =>
          let elimArg ← elimValue' arg subst
          newArgs := newArgs.push elimArg
          newArgs := newArgs.push (← invariantPredForD arg subst)
        | .value | .prop | .typeformer =>
          newArgs := newArgs.push (← elimValueOrProp' arg subst)
      return mkAppN (.const invInduct us) newArgs
  | .forallE .. =>
    if ← Meta.isTypeFormerType oldType then
      return none

    let elimType ← elimValueOrProp' oldType subst
    Meta.withLocalDeclD (n := OptionT IndInvM) `f elimType fun target => do
      let inv ←
        elimForall oldType (subst := subst)
          (fun _ e => Meta.isProof e)
          (fun value subst => elimValue value subst)
          fun dom subst args => invariantFor dom subst (mkAppN target args)
      Meta.mkLambdaFVars #[target] inv
  | .fvar fvarId =>
    let some prop ← IndInvM.getPropFor? fvarId | return none
    return subst.apply (mkFVar prop)
  | _ => return none

partial def invariantFor (oldType : Expr) (subst : Meta.FVarSubst) (target : Expr) :
    IndInvM (Option Expr) := do
  let some pred ← invariantPredFor oldType subst | return none
  return some <| mkApp pred target

end

def elim (g : MVarId) : DepM MVarId := do
  -- We know for sure that at this point in the pipeline no type arguments remain so running this
  -- monad empty is fine.
  let g ← mapExtendMVarId g (IndInvM.run <| elimValueOrProp · ·) fun arg subst fvar =>
    IndInvM.run (invariantForFVar arg subst fvar)
  return g

section Decode

open Decode

abbrev DecodeM := ReaderT DecodeCtx TransforM

def decodeUninterpretedTypeInhabitant (name : String) : DecodeM String := do
  let some endPos := name.revPosOf '_' | throwError m!"Weird type inhabitant name: {name}"
  let typeName := name.extract ⟨1⟩ endPos
  let typeId := name.extract endPos name.endPos
  let decodedTypeName := (← read).decodeTable[typeName]!
  return s!"${decodedTypeName}{typeId}"

def decodeConstName (name : String) : DecodeM String := do
  if name.startsWith "$" && !name.startsWith "$$" then
    decodeUninterpretedTypeInhabitant name
  else
    match (← read).decodeTable[name]? with
    | some name =>
      let unitSet := (← read).unitSet
      if unitSet.contains name then
        return "PUnit"
      else if unitSet.contains (name.dropRight (auxiliaryUnitCtor.toString.length + 1)) then
        return "PUnit.punit"
      else
        return name
    | none => return name

instance : MonadDecode DecodeM :=
    MonadDecode.Simple.instanceFactory
      decodeConstName
      decodeConstName
      decodeUninterpretedTypeInhabitant

def decode (model : NunModel) : DecodeM NunModel :=
  MonadDecode.decodeModel model

end Decode

public def transformation : Transformation MVarId MVarId NunResult NunResult where
   st := DecodeCtx
   inner := {
    name := "ElimDep"
    encode g := do
      let (g, d)  ← elim g |>.run
      trace[nunchaku.elimdep] m!"Result: {g}"
      return (g, d)
    decode ctx res :=
      ReaderT.run (res.mapM decode) ctx
  }

end ElimDep
end Transformation
end Nunchaku
