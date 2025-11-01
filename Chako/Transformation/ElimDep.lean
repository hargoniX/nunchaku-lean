module
import Chako.Transformation.ElimDep.Impl
import Chako.Transformation.ElimDep.Decode
public import Chako.Util.Pipeline
public import Chako.Util.Model

namespace Chako
namespace Transformation
namespace ElimDep

open Lean

public def transformation : Transformation MVarId MVarId NunResult NunResult where
   st := private DecodeCtx
   inner := {
    name := "ElimDep"
    encode g := private do
      let (g, d)  ← elim g |>.run
      trace[chako.elimdep] m!"Result: {g}"
      return (g, d)
    decode ctx res := private do
      ReaderT.run (res.mapM decode) ctx
  }

end ElimDep
end Transformation
end Chako
