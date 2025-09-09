module

public import Nunchaku.Transformation.Monomorphization.Util

namespace Nunchaku
namespace Transformation
namespace Monomorphization
namespace Solve

open Lean

public def constraintsSolvable (constraints : List FlowConstraint) : Bool :=
  -- TODO
  true

structure SolveCtx where
  /--
  The (non-ground) rules that we need to apply until a fixpoint is reached.
  -/
  rules : Array FlowConstraint

abbrev FactIndex : Type := Std.HashMap FlowVariable (Std.HashSet GroundInput)

namespace FactIndex

def insert (factIndex : FactIndex) (fact : GroundConstraint) : FactIndex :=
  factIndex.alter fact.dst
    fun
      | some srcs => some <| srcs.insert fact.src
      | none => some { fact.src }

def contains (factIndex : FactIndex) (fact : GroundConstraint) : Bool :=
  factIndex[fact.dst]? |>.map (·.contains fact.src) |>.getD false

end FactIndex

structure SolveState where
  /--
  Whether the last iteration of the fixpoint solver caused a change.
  -/
  changed : Bool := false
  /--
  Ground facts that we have so far collected about the constraint system.
  Keys are destinations, the set in the value contains the sources.
  -/
  factIndex : FactIndex
  /--
  An accumulator for new facts in this iteration of the fixpoint solver.
  -/
  newFacts : List GroundConstraint := []

abbrev SolveM := ReaderT SolveCtx <| StateM SolveState


mutual

def partiallyInstantiateFlowType (arg : FlowTypeArg) (fact : GroundConstraint) : FlowTypeArg :=
  match arg with
  | .const name us args => .const name us (partiallyInstantiate args fact)
  | .index var idx =>
    if var == fact.dst then
      fact.src.args[idx]! |>.toFlowTypeArg
    else
      .index var idx

def partiallyInstantiate (args : Array FlowTypeArg) (fact : GroundConstraint) : Array FlowTypeArg :=
  args.map (partiallyInstantiateFlowType · fact)

end

@[inline]
def learnFact (fact : GroundConstraint) : SolveM Unit := do
  modify fun s => { s with newFacts := fact :: s.newFacts }

@[inline]
def getSourcesFor (dst : FlowVariable) : SolveM (Std.HashSet GroundInput) := do
  return (← get).factIndex[dst]? |>.getD {}

partial def workRule (rule : FlowConstraint) : SolveM Unit := do
  match rule.src with
  | .vec args =>
    match FlowTypeArg.findTypeVarIn args with
    | some dst =>
      -- the rule is not ground, instantiate one argument and repeat until grounded
      for src in ← getSourcesFor dst do
        let newArgs := partiallyInstantiate args { src, dst }
        -- TODO: this could be simplified with FlowInput.ofTypes if we were in a monad with mono
        -- information
        let newRule := { rule with src := .vec newArgs }
        workRule newRule
    | none =>
      -- The rule is already ground
      learnFact { src := rule.src.toGroundInput.get! , dst := rule.dst  }
  | .var dst =>
    -- we have dst ⊑ rule.dst and find src ⊑ dst
    -- -> need to forward src into rule.dst
    for src in ← getSourcesFor dst do
      learnFact { src, dst := rule.dst }

def commitNewFacts : SolveM Unit := do
  for fact in (← get).newFacts do
    modify fun { factIndex, changed, newFacts } =>
      let contains := factIndex.contains fact
      let factIndex := factIndex.insert fact
      { factIndex, changed := changed || !contains, newFacts }
  modify fun s => { s with newFacts := [] }

def step : SolveM Unit := do
  for rule in (← read).rules do
    workRule rule
  commitNewFacts

partial def fixpoint : SolveM Unit := do
  modify fun s => { s with changed := false }
  step
  if (← get).changed then
    fixpoint
  else
    return ()

public partial def solveConstraints (constraints : List FlowConstraint)
    (_h : constraintsSolvable constraints) :
    Std.HashMap FlowVariable (List GroundInput) := Id.run do
  let mut facts := {}
  let mut rules := #[]
  for constraint in constraints do
    match constraint.src.toGroundInput with
    | some ground => facts := facts.insert ⟨ground, constraint.dst⟩
    | none => rules := rules.push constraint
  let (_, st) := fixpoint |>.run { rules } |>.run { factIndex := facts }
  let mut solution := {}
  for (dst, srcs) in st.factIndex do
    solution := solution.insert dst srcs.toList
  return solution

end Solve
end Monomorphization
end Transformation
end Nunchaku
