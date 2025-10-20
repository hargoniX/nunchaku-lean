module

public import Nunchaku.Util.Pipeline
public import Nunchaku.Util.NunchakuSyntax
public import Nunchaku.Util.Model
import Nunchaku.Transformation.Falsify
import Nunchaku.Transformation.Skolemization
import Nunchaku.Transformation.ElimComfort
import Nunchaku.Transformation.AbstractTypes
import Nunchaku.Transformation.Monomorphization
import Nunchaku.Transformation.Approximation
import Nunchaku.Transformation.ElimDep
import Nunchaku.Transformation.Output


namespace Nunchaku
namespace Transformation

public def pipeline : Pipeline Lean.MVarId NunProblem NunResult NunResult :=
  .compose Falsify.transformation <|
  .compose ElimComfort.transformation <|
  .compose AbstractTypes.transformation <|
  .compose ElimDep.transformation <|
  .compose Monomorphization.transformation <|
  .tip Output.transformation

end Transformation
end Nunchaku
