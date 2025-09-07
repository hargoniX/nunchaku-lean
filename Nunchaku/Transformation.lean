module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.NunchakuSyntax
public import Nunchaku.Util.Model
import Nunchaku.Transformation.Falsify
import Nunchaku.Transformation.Skolemization
import Nunchaku.Transformation.ElimLevels
import Nunchaku.Transformation.AbstractTypes
import Nunchaku.Transformation.Monomorphization
import Nunchaku.Transformation.Approximation
import Nunchaku.Transformation.Elimination
import Nunchaku.Transformation.Output


namespace Nunchaku
namespace Transformation

public def pipeline : Pipeline Lean.MVarId NunProblem NunResult LeanResult :=
  .compose Falsify.transformation <|
  .compose ElimLevels.transformation <|
  .compose AbstractTypes.transformation <|
  .compose Monomorphization.transformation <|
  .tip Output.transformation

end Transformation
end Nunchaku
