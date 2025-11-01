module
public import Chako.Util.TransforM
public import Lean.Meta.Tactic.FVarSubst
import Chako.Util.AddDecls

namespace Chako
namespace Transformation
namespace ElimDep

open Lean

public def auxiliaryUnitCtor : Name := `unit

/--
The different relevant groups of expressions for us.
-/
public inductive ExprKind where
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
public inductive ArgKind where
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

public def isValue (k : ArgKind) : Bool := k matches .value
public def isProof (k : ArgKind) : Bool := k matches .proof
public def isProp (k : ArgKind) : Bool := k matches .prop
public def isType (k : ArgKind) : Bool := k matches .type

public def isInductiveErasable (k : ArgKind) : Bool :=
  k.isProof || k.isValue || k.isProp

end ArgKind

public structure DepState where
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
  Cache for casesOns and matchers specialised to some particular motive and parameter set.
  -/
  matchLikeCache : Std.HashMap (Name × Array Expr × Expr) Expr := {}
  /--
  PUnit defines a type which has a universe argument that is not determined through type parameters.
  This is fundamentally at odds with our monomorphisation pass. While more types like this exist we
  decided to just special case PUnit for now by creating concrete unit-like-types for each of them
  until a more complete solution is found.
  -/
  unitCache : Std.HashMap Nat Name := {}

public abbrev DepM := StateRefT DepState TransforM

public structure DecodeCtx where
  decodeTable : Std.HashMap String String
  unitSet : Std.HashSet String

public def DepM.run (x : DepM α) : TransforM (α × DecodeCtx) := do
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

public def getKind (e : Expr) : DepM ExprKind := do
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

public def isProof (e : Expr) : DepM Bool := do
  return (← getKind e) == .proof

public def isProp (e : Expr) : DepM Bool := do
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
public def unfoldTypeAliases (e : Expr) : MetaM Expr := do
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
public def argStencil (info : ConstantVal) : DepM (Array ArgKind) := do
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
      else if ← Meta.isType arg then
        drop := drop.push .type
      else if ← Meta.isTypeFormerType argType then
        drop := drop.push .typeformer
      else
        drop := drop.push .value

    return drop

  modify fun s => { s with argCache := s.argCache.insert info.name stencil }
  return stencil

public def elimCtorName (inductElimName : Name) (ctorName : Name) : MetaM Name := do
  let .str _ n := ctorName | throwError m!"Weird ctor name {ctorName}"
  return .str inductElimName n

/--
Correct a projection index of a structure by accounting for the fact that proofs were dropped from
it.
-/
public def correctProjIndex (typeName : Name) (idx : Nat) : DepM Nat := do
  let inductInfo ← getConstInfoInduct typeName
  let ctorName := inductInfo.ctors[0]!
  let inductStencil ← argStencil inductInfo.toConstantVal
  let ctorStencil ← argStencil (← getConstVal ctorName)
  let ctorStencil := ctorStencil.drop inductStencil.size
  let slice := ctorStencil[0...idx].toArray
  let newIdx := idx - slice.countP ArgKind.isProof
  trace[chako.elimdep] m!"Adjusting projection on {typeName} from {idx} to {newIdx}"
  return newIdx

@[inline]
public partial def elimExtendForall' [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
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
public partial def elimExtendForall [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (expr : Expr) (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (extender : Expr → Meta.FVarSubst → FVarId → m (Option Expr))
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr)
    (subst : Meta.FVarSubst := {}) : m Expr := do
  Meta.forallTelescope expr fun args body => do
    elimExtendForall' args body dropArg argHandler extender bodyHandler subst

@[inline]
public partial def elimForall' [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (args : Array Expr) (body : Expr)
    (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr) (subst : Meta.FVarSubst := {}) :
    m Expr := do
  elimExtendForall' args body dropArg argHandler (fun _ _ _ => return none) bodyHandler subst

@[inline]
public partial def elimForall [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [MonadLiftT DepM m]
    (expr : Expr) (dropArg : Nat → Expr → m Bool)
    (argHandler : Expr → Meta.FVarSubst → m Expr)
    (bodyHandler : Expr → Meta.FVarSubst → Array Expr → m Expr)
    (subst : Meta.FVarSubst := {}) : m Expr := do
  Meta.forallTelescope expr fun args body => do
    elimForall' args body dropArg argHandler bodyHandler subst

end ElimDep
end Transformation
end Chako
