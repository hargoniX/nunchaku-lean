module

import Lean.Meta.Basic
public import Chako.Util.TransforM

/-!
This module contains the definition of an abstract notion of a reduction pipeline.
-/

namespace Chako

open Lean

public section

structure TransformationInner (a b c d st : Type) where
  name : String
  encode : a → TransforM (b × st)
  decode : st → c → TransforM d

structure Transformation (a b c d : Type) where
  {st : Type}
  inner : TransformationInner a b c d st

inductive Pipeline : Type → Type → Type → Type → Type _ where
  | tip (trans : Transformation a b c d) : Pipeline a b c d
  | compose (trans : Transformation a b e f) (pipe : Pipeline b c d e) : Pipeline a c d f

namespace Pipeline

def run (pipe : Pipeline a b c d) (x : a) : TransforM (b × (c → TransforM d)) := do
  match pipe with
  | .tip trans =>
    let (transformed, st) ←
      withTraceNode `nunchaku (fun _ => return m!"Running transformation: {trans.inner.name}") do
        trans.inner.encode x
    return (transformed, fun res => trans.inner.decode st res)
  | .compose start remainder =>
    let (transformed, st) ←
      withTraceNode `nunchaku (fun _ => return m!"Running transformation: {start.inner.name}") do
        start.inner.encode x
    let (transformed, back) ← remainder.run transformed
    let fullBack res := do
      let step ← back res
      start.inner.decode st step
    return (transformed, fullBack)

end Pipeline

end

end Chako
