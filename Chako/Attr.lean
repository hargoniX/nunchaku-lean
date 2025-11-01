module

import Lean.Data.Options
import Lean.Util.Trace
public import Lean.Elab.Tactic.Config

/-!
This module contains declarations of environment extensions etc. used in the `chako` tactic.
-/

open Lean

namespace Chako

initialize registerTraceClass `chako
initialize registerTraceClass `chako.solver (inherited := true)
initialize registerTraceClass `chako.equations (inherited := true)
initialize registerTraceClass `chako.falsify (inherited := true)
initialize registerTraceClass `chako.elimdep (inherited := true)
initialize registerTraceClass `chako.elimcomfort (inherited := true)
initialize registerTraceClass `chako.abstract (inherited := true)
initialize registerTraceClass `chako.mono (inherited := true)
initialize registerTraceClass `chako.output (inherited := true)

public section

inductive ChakoConfig.Solvers where
  | cvc4
  | smbc
  | kodkod

def ChakoConfig.Solvers.toCliArg : Solvers → String
  | .cvc4 => "cvc4"
  | .smbc => "smbc"
  | .kodkod => "kodkod"

/--
The configuration options for `chako`.
-/
structure ChakoConfig where
  /-- The number of seconds that the model finder is run before aborting. -/
  timeout : Nat := 10
  /-- Whether to look for a counter-model, if set to `false` looks for a model instead. -/
  falsify : Bool := true
  /-- The list of portfolio solvers to try. -/
  solvers : Array ChakoConfig.Solvers := #[.cvc4, .smbc, .kodkod]

declare_config_elab elabChakoConfig Chako.ChakoConfig

/--
Invoke the external model finder Nunchaku in an attempt to find a counter example for the current
goal state.
-/
syntax (name := chakoStx) "chako" Lean.Parser.Tactic.optConfig : tactic

end

end Chako
