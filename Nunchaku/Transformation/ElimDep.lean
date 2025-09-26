module
public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.Model
import Nunchaku.Util.LocalContext
import Nunchaku.Util.AddDecls
import Lean.Meta.CollectFVars

namespace Nunchaku
namespace Transformation
namespace ElimDep

open Lean

inductive ExprKind where
  | proof
  | prop
  | other
  deriving Inhabited, Repr, DecidableEq

structure DepState where
  argCache : Std.HashMap Name (Array Nat) := {}
  constCache : Std.HashMap Name Name := {}
  newEquations : Std.HashMap Name (List Expr) := {}
  invCache : Std.HashMap Name Name := {}
  exprKindCache : Std.HashMap Expr ExprKind := {}
  elimCache : Std.HashMap (Expr × Bool) Expr := {}

abbrev DepM := StateRefT DepState TransforM


def isProof (e : Expr) : DepM Bool := do
  match (← get).exprKindCache[e]? with
  | some k => return k == .proof
  | none =>
    if ← Meta.isProof e then
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .proof }
      return true
    else if ← Meta.isProp e then
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .prop }
      return false
    else
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .other }
      return false

def isProp (e : Expr) : DepM Bool := do
  match (← get).exprKindCache[e]? with
  | some k => return k == .prop
  | none =>
    if ← Meta.isProp e then
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .prop }
      return true
    else if ← Meta.isProof e then
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .proof }
      return false
    else
      modify fun s => { s with exprKindCache := s.exprKindCache.insert e .other }
      return false

def shouldElim (e : Expr) : DepM Bool := do
  isProof e

def argStencil (info : ConstantVal) : DepM (Array Nat) := do
  if let some stencil := (← get).argCache[info.name]? then
    return stencil

  let stencil ← Meta.forallTelescope info.type fun args _ => do
    let mut drop := #[]
    for idx in 0...args.size do
      let arg := args[idx]!
      if ← shouldElim arg then
        drop := drop.push idx

    return drop

  modify fun s => { s with argCache := s.argCache.insert info.name stencil }
  return stencil

def filterWithStencil (stencil : Array Nat) (xs : Array α) : Array α := Id.run do
  let mut new := #[]
  for h : idx in 0...xs.size do
    -- TODO: quadratic
    if !stencil.contains idx then
      new := new.push xs[idx]
  new

-- TODO: dedup with specialise
def elimCtorName (inductElimName : Name) (ctorName : Name) : MetaM Name := do
  let .str _ n := ctorName | throwError m!"Weird ctor name {ctorName}"
  return .str inductElimName n

def correctProjIndex (typeName : Name) (idx : Nat) : DepM Nat := do
  let inductInfo ← getConstInfoInduct typeName
  let ctorName := inductInfo.ctors[0]!
  let inductStencil ← argStencil inductInfo.toConstantVal
  let ctorStencil ← argStencil (← getConstVal ctorName)
  let ctorStencil := ctorStencil.drop inductStencil.size
  let offset := ctorStencil.countP (· < idx)
  assert! idx >= offset
  return idx - offset

def maxLit : Nat := 2^16

def isNonPropTypeFormer (expr : Expr) : MetaM Bool := do
  let some level ← Meta.typeFormerTypeLevel expr | return false
  return level != 0

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

def unfoldTypeAliases (e : Expr) : MetaM Expr := do
  Meta.transform e (pre := pre)
where
  pre (expr : Expr) : MetaM TransformStep := do
    let .const name _ := expr.getAppFn | return .continue
    if ! (← isTypeAlias name) then return .continue
    let some expr ← Meta.unfoldDefinition? expr (ignoreTransparency := true)
      | throwError m!"Failed to unfold type alias {expr}"
    return .visit expr

@[inline]
partial def elimForall' [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (args : Array Expr) (body : Expr)
    (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr) (subst : Meta.FVarSubst := {}) :
    m Expr := do
  go args body 0 #[] subst
where
  @[specialize]
  go (args : Array Expr) (body : Expr) (idx : Nat) (acc : Array Expr) (subst : Meta.FVarSubst) :
      m Expr := do
    if h : idx < args.size then
      let arg := args[idx]
      if ← dropArg idx arg then
        go args body (idx + 1) acc subst
      else
        let arg := args[idx]
        let fvar := arg.fvarId!
        let newType ← argHandler (← fvar.getType) subst
        Meta.withLocalDecl (← fvar.getUserName) (← fvar.getBinderInfo) newType fun newArg => do
          let subst := subst.insert fvar newArg
          go args body (idx + 1) (acc.push newArg) subst
    else
      let newBody ← bodyHandler body subst acc
      let newExpr ← Meta.mkForallFVars acc newBody
      return newExpr

@[inline]
partial def elimForall [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (expr : Expr) (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr)
    (subst : Meta.FVarSubst := {}) : m Expr := do
  Meta.forallTelescope expr fun args body => do
    elimForall' args body dropArg argHandler bodyHandler subst

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
        let arg := args[idx]
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

mutual

/--
Invariant: Never called on proofs
-/
partial def elimValueOrPop' (expr : Expr) (subst : Meta.FVarSubst) : DepM Expr := do
  -- TODO: remove debug
  if ← isProof expr then
    throwError m!"Called on proof: {expr}"

  if ← isProp expr then
    elimProp' expr subst
  else
    elimValue' expr subst

partial def elimExpr' (expr : Expr) (inProp : Bool) (subst : Meta.FVarSubst) : DepM Expr := do
  if let some cached := (← get).elimCache[(expr, inProp)]? then
    return cached
  else
    let finishedExpr ← elimExprRaw' expr inProp subst
    modify fun s => { s with elimCache := s.elimCache.insert (expr, inProp) finishedExpr }
    return finishedExpr

partial def elimExprRaw' (expr : Expr) (inProp : Bool) (subst : Meta.FVarSubst) : DepM Expr := do
  trace[nunchaku.elimdep] m!"elimExpr': {expr}, prop?: {inProp}"
  if inProp && !(← isProp expr) then
    throwError m!"Called on non prop: {expr}"

  if !inProp && (← isProof expr <||> isProp expr) then
    throwError m!"Called on proof or prop: {expr}"

  match expr with
  | .const const us =>
    if TransforM.isBuiltin const then
      return .const const us

    let const ← elimConst const
    return .const const us
  | .app .. =>
    expr.withApp fun fn args => do
      match fn with
      | .const fn us =>
        if TransforM.isBuiltin fn then
          let args ← args.mapM (elimValueOrPop' · subst)
          return mkAppN (.const fn us) args
        else
          let fn ← elimConst fn
          let args ← args.filterMapM (elimValuePropNoProof · subst)
          return mkAppN (.const fn us) args
      | _ =>
        let fn ← elimValue' fn subst
        let args ← args.filterMapM (elimValuePropNoProof · subst)
        return mkAppN fn args
  | .lam .. =>
    Meta.lambdaBoundedTelescope expr 1 fun args body => do
      let arg := args[0]!
      if ← isProof arg then
        elimValueOrPop' body subst
      else
        let fvarId := arg.fvarId!
        let name ← fvarId.getUserName
        let bi ← fvarId.getBinderInfo
        let newType ← elimValue' (← fvarId.getType) subst

        Meta.withLocalDecl name bi newType fun replacedArg => do
          let newBody ← elimValueOrPop' body (subst.insert fvarId replacedArg)
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
        let newType ← elimValueOrPop' (← fvarId.getType) subst

        Meta.withLocalDecl name bi newType fun replacedArg => do
          let newBody ← elimExpr' body inProp (subst.insert fvarId replacedArg)
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
        let newValue ← elimValueOrPop' (← fvarId.getValue?).get! subst

        Meta.withLetDecl name newType newValue (nondep := nondep) fun replacedArg => do
          let newBody ← elimExpr' body inProp (subst.insert fvarId replacedArg)
          Meta.mkLetFVars #[replacedArg] newBody
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
partial def elimProp' (expr : Expr) (subst : Meta.FVarSubst) : DepM Expr := do
  elimExpr' expr true subst

partial def elimValuePropNoProof (expr : Expr) (subst : Meta.FVarSubst) : DepM (Option Expr) := do
  if ← isProof expr then
    return none
  else
    return some (← elimValueOrPop' expr subst)

/--
Invariant: Never called on a proof or proposition.
-/
partial def elimValue' (expr : Expr) (subst : Meta.FVarSubst) : DepM Expr := do
  elimExpr' expr false subst

partial def elimValueOrProp (expr : Expr) (subst : Meta.FVarSubst) : DepM Expr := do
  let expr ← unfoldTypeAliases expr
  elimValueOrPop' expr subst

partial def elimValue (expr : Expr) (subst : Meta.FVarSubst) : DepM Expr := do
  let expr ← unfoldTypeAliases expr
  elimValue' expr subst

partial def elimProp (expr : Expr) (subst : Meta.FVarSubst) : DepM Expr := do
  let expr ← unfoldTypeAliases expr
  elimProp' expr subst

partial def elimConstType (expr : Expr) (stencil : Array Nat) : DepM Expr := do
  -- TODO: quadratic
  elimForall expr (fun idx _ => return stencil.contains idx) elimValue (fun b s _ => elimValue b s)

partial def elimPropCtor (inductElimName : Name) (inductStencil : Array Nat) (ctorName : Name) :
    DepM Constructor := do
  let info ← getConstVal ctorName
  let elimName ← elimCtorName inductElimName ctorName
  let elimType ← elimForall info.type (fun _ _ => return false) elimValueOrProp
    fun body subst _ =>
      body.withApp fun origInduct args => do
        let .const _ us := origInduct | throwError m!"Weird ctor: {ctorName}"
        let mut freshArgs := #[]
        for idx in 0...args.size do
          -- TODO: quadratic
          if inductStencil.contains idx then
            continue
          let arg ← elimValue args[idx]! subst
          freshArgs := freshArgs.push arg
        return mkAppN (.const inductElimName us) freshArgs

  modify fun s => { s with constCache := s.constCache.insert ctorName elimName }
  return ⟨elimName, elimType⟩

partial def elimValueCtor (inductElimName : Name) (inductStencil : Array Nat) (ctorName : Name) :
    DepM Constructor := do
  let info ← getConstVal ctorName
  let elimName ← elimCtorName inductElimName ctorName
  let stencil ← argStencil info
  -- TODO: quadratic
  let elimType ← elimForall info.type (fun idx _ => return stencil.contains idx) elimValue
    fun body subst _ =>
      body.withApp fun origInduct args => do
        let .const _ us := origInduct | throwError m!"Weird ctor: {ctorName}"
        let mut freshArgs := #[]
        for idx in 0...args.size do
          -- TODO: quadratic
          if inductStencil.contains idx then
            continue
          let arg ← elimValue args[idx]! subst
          freshArgs := freshArgs.push arg
        return mkAppN (.const inductElimName us) freshArgs

  modify fun s => { s with constCache := s.constCache.insert ctorName elimName }
  return ⟨elimName, elimType⟩

partial def elimInduct (info : InductiveVal) : DepM Unit := do
  let name := info.name
  let elimName := (← get).constCache[name]!
  let stencil ← argStencil info.toConstantVal
  let newType ← elimConstType info.type stencil
  let nparams := info.numParams - stencil.countP (· < info.numParams)
  if ← Meta.isPropFormerType info.type then
    let newCtors ← info.ctors.map
  --if ← Meta.isPropFormerType info.type then
  --  let newCtors ← info.ctors.mapM (elimPropCtor elimName stencil)

  --  let decl := {
  --    name := elimName,
  --    type := newType,
  --    ctors := newCtors
  --  }

  --  TransforM.recordDecl <| .inductDecl info.levelParams nparams [decl] false
  --else
  --  let newCtors ← info.ctors.mapM (elimValueCtor elimName stencil)

  --  let decl := {
  --    name := elimName,
  --    type := newType,
  --    ctors := newCtors
  --  }

  --  trace[nunchaku.elimdep] m!"Proposing {newType} {newCtors.map (·.type)}"

  --  TransforM.recordDecl <| .inductDecl info.levelParams nparams [decl] false

  --  discard <| invariantForInduct info

partial def elimEquation (eq : Expr) : DepM Expr := do
  trace[nunchaku.elimdep] m!"Working eq {eq}"
  Meta.forallTelescope eq fun args body => do
    let (_, { fvarSet, .. }) ← body.collectFVars |>.run {}
    let shouldDrop := fun _ arg => do
      if ← isProof arg then
        return fvarSet.contains arg.fvarId!
      else
        return false
    let res ← elimForall' args body shouldDrop elimValueOrProp (fun b s _ => elimProp b s)
    trace[nunchaku.elimdep] m!"New equation: {res}"
    return res

partial def elimDefn (info : DefinitionVal) : DepM Unit := do
  let name := info.name
  let elimName := (← get).constCache[name]!
  if ← isProp info.type then
    throwError m!"Proofs should be erased but tried to work: {info.name}"

  let stencil ← argStencil info.toConstantVal
  let u ← Meta.getLevel info.type
  let newType ← elimConstType info.type stencil
  trace[nunchaku.elimdep] m!"New type for {info.name}: {newType}"

  let decl := {
    name := elimName,
    levelParams := info.levelParams,
    type := newType,
    value := mkApp (mkConst ``TransforM.sorryAx [u]) newType,
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
  let newType ← elimConstType info.type stencil

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

partial def ctorToInvariant (inductInvName : Name) (inductStencil : Array Nat) (ctorName : Name) : DepM Constructor := do
  let info ← getConstVal ctorName
  let ctorStencil ← argStencil info
  let elimName ← elimCtorName inductInvName ctorName
  let elimType ← Meta.forallTelescope info.type fun args body => do
    let handleBody body subst changedFVars := do
      let lparams := info.levelParams.map .param
      let args ← body.withApp fun _ args => do
        let args := filterWithStencil inductStencil args
        args.mapM (elimValueOrProp · subst)
      let elimCtorName ← elimConst ctorName
      let ctorArgs := filterWithStencil ctorStencil changedFVars
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
  let invType ← Meta.forallTelescope info.type fun args _ => do
    let valueTy ← Meta.mkAppM name args
    Meta.withLocalDecl `ind .default valueTy fun arg =>
      let args := args.push arg
      elimForall' args (.sort 0) (fun _ arg => isProof arg) elimValue (fun e _ _ => return e)

  let stencil ← argStencil info.toConstantVal

  let invCtors := ← info.ctors.mapM (ctorToInvariant invName stencil)
  let decl := {
    name := invName,
    type := invType,
    ctors := invCtors,
  }
  trace[nunchaku.elimdep] m!"Proposing inv {invType} {invCtors.map (·.type)}"

  -- TODO: introduce recursive parameters
  let nparams := info.numParams - stencil.countP (· < info.numParams)
  TransforM.recordDecl <| .inductDecl info.levelParams nparams [decl] false
  return invName

partial def invariantForFVar (oldType : Expr) (subst : Meta.FVarSubst) (newFVar : FVarId) :
    DepM (Option Expr) :=
  invariantFor oldType subst (mkFVar newFVar)

partial def invariantFor (oldType : Expr) (subst : Meta.FVarSubst) (target : Expr) :
    DepM (Option Expr) := do
  if ← isProp oldType then
    return none
  -- TODO: dedup with comfort
  let oldType ← Meta.zetaReduce oldType
  let oldType ← Core.betaReduce oldType
  -- TODO: check if needed
  let oldType ← unfoldTypeAliases oldType
  let oldType := oldType.consumeMData
  match oldType with
  | .const .. | .app .. =>
    oldType.withApp fun fn args => do
      let .const fn us := fn | return none
      let .inductInfo info ← getConstInfo fn | return none
      let invInduct ← invariantForInduct info
      let args ← args.filterMapM fun arg => do
        if ← isProof arg then
          return none
        else
          return some <| (← elimValueOrPop' arg subst)
      let args := args.push target
      return mkAppN (.const invInduct us) args
  | .forallE .. =>
    if ← Meta.isTypeFormerType oldType then
      return none

    elimForall (m := OptionT DepM) oldType (subst := subst)
      (fun _ e => Meta.isProof e)
      (fun value subst => elimValue value subst)
      fun dom subst args => invariantFor dom subst (mkAppN target args)
  | _ => return none

end

def elim (g : MVarId) : DepM MVarId := do
  let g ← mapExtendMVarId g elimValueOrProp invariantForFVar
  TransforM.replaceEquations (← get).newEquations
  TransforM.addDecls
  return g

public def transformation : Transformation MVarId MVarId LeanResult LeanResult where
   st := private Unit
   inner := private {
    name := "ElimDep"
    encode g := do
      let g ← elim g |>.run' {}
      trace[nunchaku.elimdep] m!"Result: {g}"
      return (g, ())
    decode _ res := return res
  }

end ElimDep
end Transformation
end Nunchaku
