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

public partial def solveConstraints (constraints : List FlowConstraint)
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


end Solve
end Monomorphization
end Transformation
end Nunchaku
