import Nunchaku.Util.Pipeline
import Nunchaku.Util.NunchakuSyntax
import Nunchaku.Util.Model

namespace Nunchaku
namespace Transformation
namespace Output

def transformation : Transformation Lean.MVarId NunProblem NunResult LeanResult where
  st := Unit
  inner := {
    name := "Output"
    encode g := return ({ commands := [] }, ())
    decode _ res := do
      match res with
      | .unsat => return .unsat
      | .unknown => return .unknown
      -- TODO: proper model recovery
      | .sat model => return .sat []
  }


end Output
end Transformation
end Nunchaku
