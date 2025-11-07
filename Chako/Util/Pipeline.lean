module

import Lean.Meta.Basic
public import Chako.Util.TransforM

/-!
This module contains the definition of an abstract notion of a reduction pipeline.
-/

namespace Chako

open Lean

/--
The description of a transformation step.
-/
public structure TransformationInner (a b c d st : Type) where
  /--
  The name of the transformation.
  -/
  name : String
  /--
  The encoding step of the transformation, producing both the output type as well as an element of
  `st` which will be passed back into the `decode` function.
  -/
  encode : a → TransforM (b × st)
  /--
  The decoding step, taking both the decoding state `st` as well as the actual object to decode.
  -/
  decode : st → c → TransforM d

/--
A transformation step within a pipeline. Each step carries an existential type `st` that it can use
to create information in the encoding step that will be passed into the decoding step.
-/
public structure Transformation (a b c d : Type) where
  {st : Type}
  inner : TransformationInner a b c d st

/--
A `Pipeline α β γ δ` takes in some problem of type `α`, producing a problem of type `β` and
eventually accepts back a result of type `γ` decoding it to some result of type `δ`.
-/
public inductive Pipeline : Type → Type → Type → Type → Type _ where
  /--
  The tip of a pipeline, this transformation is going to be responsible for doing the final encoding
  step, then produce a result and decode that back for the remainder of the pipeline to consume.
  -/
  | tip (trans : Transformation a b c d) : Pipeline a b c d
  /--
  Adding an additional transformation infront of an already existing pipe.
  -/
  | compose (trans : Transformation a b e f) (pipe : Pipeline b c d e) : Pipeline a c d f

namespace Pipeline

/--
Execute `pipe` on some input problem `x`, returning both the output value from the pipeline as well
as a continuation that can be called to recover the result back into the original result type.
-/
public def run (pipe : Pipeline a b c d) (x : a) : TransforM (b × (c → TransforM d)) := do
  match pipe with
  | .tip trans =>
    let (transformed, st) ←
      withTraceNode `chako (fun _ => return m!"Running transformation: {trans.inner.name}") do
        trans.inner.encode x
    return (transformed, fun res => trans.inner.decode st res)
  | .compose start remainder =>
    let (transformed, st) ←
      withTraceNode `chako (fun _ => return m!"Running transformation: {start.inner.name}") do
        start.inner.encode x
    let (transformed, back) ← remainder.run transformed
    let fullBack res := do
      let step ← back res
      start.inner.decode st step
    return (transformed, fullBack)

end Pipeline

end Chako
