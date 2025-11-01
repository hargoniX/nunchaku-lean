module

public import Chako.Util.Pipeline
public import Chako.Util.Model

/-!
This module contains the transformation for negating the goal should that be necessary.
-/

namespace Chako
namespace Transformation
namespace Falsify

public def transformation : Transformation Lean.MVarId Lean.MVarId NunResult NunResult where
  st := private Unit
  inner := private {
    name := "Falsify"
    encode g := g.withContext do
      if (← read).falsify then
        let g := (← Lean.Meta.mkFreshExprMVar (Lean.mkNot (← g.getType))).mvarId!
        trace[nunchaku.falsify] m!"Result: {g}"
        return (g, ())
      else
        trace[nunchaku.falsify] m!"Result: {g}"
        return (g, ())
    decode _ res := return res
  }

end Falsify
end Transformation
end Chako
