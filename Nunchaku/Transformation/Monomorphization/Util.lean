module

public import Lean.Meta.Basic
public import Nunchaku.Util.TransforM

namespace Nunchaku
namespace Transformation
namespace Monomorphization

open Lean

public section

structure FlowVariable where
  function : Name
  deriving Inhabited, BEq, Hashable

instance : ToString FlowVariable where
  toString var := Name.toString var.function

/--
A non ground type argument.
-/
inductive FlowTypeArg where
  /--
  Projecting a particular type out of a flow variable.
  -/
  | index (var : FlowVariable) (idx : Nat)
  /--
  A (potentially polymorphic) type with arguments.
  -/
  | const (name : Name) (args : Array FlowTypeArg)
  /--
  A (non polymorphic) function type
  -/
  | func (dom codom : FlowTypeArg)
  deriving Inhabited, BEq, Hashable

def FlowTypeArg.findTypeVar (type : FlowTypeArg) : Option FlowVariable :=
  match type with
  | .index var .. => some var
  | .const _ args => Id.run do
    for arg in args do
      if let some var := findTypeVar arg then
        return some var
    return none
  | .func dom codom => dom.findTypeVar <|> codom.findTypeVar

def FlowTypeArg.findTypeVarIn (types : Array FlowTypeArg) : Option FlowVariable := Id.run do
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
    | .func dom codom => m!"{go dom} → {go codom}"

/--
The inputs into a flow variable.
-/
inductive FlowInput where
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
structure FlowConstraint where
  src : FlowInput
  dst : FlowVariable
  deriving Inhabited, BEq, Hashable

instance : ToMessageData FlowConstraint where
  toMessageData constr := m!"{toMessageData constr.src} ⊑ {toMessageData constr.dst}"

/--
A ground type argument.
-/
inductive GroundTypeArg where
  /--
  A list of ground type arguments applied to a constant are ground.
  -/
  | const (name : Name) (args : Array GroundTypeArg)
  /--
  A function between ground type arguments is ground
  -/
  | func (dom codom : GroundTypeArg)
  deriving Inhabited, BEq, Hashable

instance : ToMessageData GroundTypeArg where
  toMessageData := go
where
  go (arg : GroundTypeArg) : MessageData :=
    match arg with
    | .const name args => m!"{toMessageData name} {args.map go}"
    | .func dom codom => m!"{go dom} → {go codom}"

/--
An assignment to a vector of type variables.
-/
structure GroundInput where
  args : Array GroundTypeArg
  deriving Inhabited, BEq, Hashable

instance : ToMessageData GroundInput where
  toMessageData i := toMessageData i.args

/--
The type arguments of `dst` are instantiated using the ground type arguments in `src`.
-/
structure GroundConstraint where
  src : GroundInput
  dst : FlowVariable
  deriving Inhabited, BEq, Hashable

def FlowTypeArg.toGroundTypeArg (type : FlowTypeArg) : Option GroundTypeArg := do
  match type with
  | .const name args => return .const name (← args.mapM FlowTypeArg.toGroundTypeArg)
  | .index .. => none
  | .func dom codom => return .func (← dom.toGroundTypeArg) (← codom.toGroundTypeArg)

def FlowInput.toGroundInput (inp : FlowInput) : Option GroundInput := do
  match inp with
  | .var .. => none
  | .vec args =>
    return ⟨← args.mapM FlowTypeArg.toGroundTypeArg⟩

def GroundTypeArg.toFlowTypeArg (arg : GroundTypeArg) : FlowTypeArg :=
  match arg with
  | .const name args => .const name (args.map GroundTypeArg.toFlowTypeArg)
  | .func dom codom => .func dom.toFlowTypeArg codom.toFlowTypeArg

partial def GroundTypeArg.toExpr (arg : GroundTypeArg) : MetaM Expr := do
  match arg with
  | .const name args => Meta.mkAppOptM name (← args.mapM fun arg => return some (← arg.toExpr))
  | .func dom codom => mkArrow (← dom.toExpr) (← codom.toExpr)


structure MonoAnalysisState where
  /--
  Which of the arguments of a function `f` are type arguments that we consider for monomorphisation.
  -/
  argPos : Std.HashMap Name (Array Nat) := {}

abbrev MonoAnalysisM := StateRefT MonoAnalysisState TransforM

def MonoAnalysisM.run (x : MonoAnalysisM α) : TransforM (α × MonoAnalysisState) :=
  StateRefT'.run x {}

def getMonoArgPositions (const : Name) : MonoAnalysisM (Array Nat) := do
  if let some cached := (← getThe MonoAnalysisState).argPos[const]? then
    return cached

  let ty := (← getConstVal const).type
  Meta.forallTelescope ty fun args _ => do
    let mut positions := #[]
    for h : idx in 0...args.size do
      let type ← Meta.inferType args[idx]
      let .sort lvl := type
        | continue
      if !lvl.isAlwaysZero then
        positions := positions.push idx

    modifyThe MonoAnalysisState fun s => { s with argPos := s.argPos.insert const positions }

    return positions

end

end Monomorphization
end Transformation
end Nunchaku
