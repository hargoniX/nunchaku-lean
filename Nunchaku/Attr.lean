import Lean.Data.Options
import Lean.Util.Trace

/-!
This module contains declarations of environment extensions etc. used in the `nunchaku` tactic.
-/

open Lean

namespace Nunchaku

initialize registerTraceClass `nunchaku

inductive NunchakuConfig.Solvers where
  | cvc4

/--
The configuration options for `nunchaku`.
-/
structure NunchakuConfig where
  /-- The number of seconds that the model finder is run before aborting. -/
  timeout : Nat := 10
  /-- Whether to look for a counter-model, if set to `false` looks for a model instead. -/
  falsify : Bool := true
  /-- The list of portfolio solvers to try. -/
  solvers : Array NunchakuConfig.Solvers := #[.cvc4]

/--
Invoke the external model finder Nunchaku in an attempt to find a counter example for the current
goal state.
-/
syntax (name := nunchakuStx) "nunchaku" Lean.Parser.Tactic.optConfig : tactic

end Nunchaku
