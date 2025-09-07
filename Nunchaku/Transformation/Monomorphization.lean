import Nunchaku.Util.Pipeline
import Nunchaku.Util.Model

import Nunchaku.Transformation.Monomorphization.Collect
import Nunchaku.Transformation.Monomorphization.Solve
import Nunchaku.Transformation.Monomorphization.Specialise

/-!
This module contains the monomorphisation transformation, it is based on
["The Simple Essence of Monomorphization"](https://se.cs.uni-tuebingen.de/publications/lutze25simple.pdf)
though restricted to the simplest possible fragment in Lean for now.
-/

namespace Nunchaku
namespace Transformation
namespace Monomorphization

open Lean

open Collect Solve Specialise

def transformation : Transformation MVarId MVarId LeanResult LeanResult where
  st := Unit
  inner := {
    name := "Monomorphisation"
    encode g := g.withContext do
      let (constraints, monoAnalysis) ← (collectConstraints g).run
      if h : !constraintsSolvable constraints then
        throwError "The goal cannot be monomorphised."
      else
        trace[nunchaku.mono] m!"Constraints: {constraints}"
        let solution := solveConstraints constraints (by simpa using h)
        trace[nunchaku.mono] m!"Solution: {solution.toList}"
        let (g, st) ← (specialize g).run { solution } monoAnalysis
        TransforM.replaceEquations st.newEquations
        trace[nunchaku.mono] m!"Result: {g}"
        return (g, ())
    decode _ res := return res
  }

end Monomorphization
end Transformation
end Nunchaku
