import Lean.Expr
import Lean.Message
/-!
This module contains the definition of a Nunchaku result, including the kind of models
nunchaku is capable of returning.
-/

namespace Nunchaku

inductive SolverResult (α : Type) where
  | unsat
  | unknown
  | sat (x : α)

-- TODO: Proper model
abbrev NunResult := SolverResult Unit
abbrev LeanResult := SolverResult (List (Lean.Name × Lean.Expr))

namespace LeanResult

instance : Lean.ToMessageData LeanResult where
  toMessageData res :=
    -- TODO
    match res with
    | .unsat => "The prover is convinced that the theorem is true."
    | .unknown => "The prover wasn't able to prove or disprove the theorem."
    | .sat _ => "The prover found a counter example"

end LeanResult

end Nunchaku
