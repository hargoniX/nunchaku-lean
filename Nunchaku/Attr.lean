module

import Lean.Data.Options
import Lean.Util.Trace
public import Lean.Elab.Tactic.Config

/-!
This module contains declarations of environment extensions etc. used in the `nunchaku` tactic.
-/

open Lean

namespace Nunchaku

initialize registerTraceClass `nunchaku
initialize registerTraceClass `nunchaku.solver (inherited := true)
initialize registerTraceClass `nunchaku.equations (inherited := true)
initialize registerTraceClass `nunchaku.falsify (inherited := true)
initialize registerTraceClass `nunchaku.elimcomfort (inherited := true)
initialize registerTraceClass `nunchaku.abstract (inherited := true)
initialize registerTraceClass `nunchaku.mono (inherited := true)
initialize registerTraceClass `nunchaku.output (inherited := true)

public section

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

declare_config_elab elabNunchakuConfig Nunchaku.NunchakuConfig

/--
Invoke the external model finder Nunchaku in an attempt to find a counter example for the current
goal state.
-/
syntax (name := nunchakuStx) "nunchaku" Lean.Parser.Tactic.optConfig : tactic

end

end Nunchaku
