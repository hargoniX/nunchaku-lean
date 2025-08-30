import Nunchaku.Transformation.Skolemization
import Nunchaku.Transformation.Monomorphization
import Nunchaku.Transformation.Approximation
import Nunchaku.Transformation.Elimination
import Nunchaku.Transformation.Output
import Nunchaku.Util.Pipeline
import Nunchaku.Util.NunchakuSyntax
import Nunchaku.Util.Model

namespace Nunchaku
namespace Transformation

def pipeline : Pipeline Lean.MVarId NunProblem NunResult LeanResult :=
  .tip Output.transformation

end Transformation
end Nunchaku
