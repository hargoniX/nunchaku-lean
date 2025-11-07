module

public import Chako.Util.Pipeline
public import Chako.Util.NunchakuSyntax
public import Chako.Util.Model
import Chako.Transformation.Falsify
import Chako.Transformation.Skolemization
import Chako.Transformation.ElimComfort
import Chako.Transformation.AbstractTypes
import Chako.Transformation.Monomorphization
import Chako.Transformation.Approximation
import Chako.Transformation.ElimDep
import Chako.Transformation.Output

/-!
This module contains the core transformation pipeline of Chako.
-/

namespace Chako
namespace Transformation

public def pipeline : Pipeline Lean.MVarId NunProblem NunResult NunResult :=
  .compose ElimComfort.transformation <|
  .compose Falsify.transformation <|
  .compose AbstractTypes.transformation <|
  .compose ElimDep.transformation <|
  .compose Monomorphization.transformation <|
  .tip Output.transformation

end Transformation
end Chako
