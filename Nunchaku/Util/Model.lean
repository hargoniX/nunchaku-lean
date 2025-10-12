module

public import Lean.Expr
public import Lean.Message
public import Nunchaku.Util.Sexp
public import Nunchaku.Util.NunchakuSyntax
import Nunchaku.Util.NunchakuBuilder
import Nunchaku.Util.NunchakuPrinter
import Std.Data.TreeSet.Basic

/-!
This module contains the definition of a Nunchaku result, including the kind of models
nunchaku is capable of returning.
-/

namespace Nunchaku

public section

inductive SolverResult (α : Type) where
  | unsat
  | unknown
  | sat (x : α)

inductive NunModelDecl where
  | type (name : String) (members : List String)
  | val (name : String) (value : NunTerm)

namespace NunModelDecl

private def parseTerm (t : Sexp) : Except String NunTerm := do
  go t |>.run {}
where
  go (t : Sexp) : ReaderT (Std.TreeSet String (cmp := compare)) (Except String) NunTerm := do
    match t with
    | .atom "true" => return .builtin .true
    | .atom "false" => return .builtin .false
    | .atom id =>
      if (← read).contains id then
        return .var id
      else
        return .const id
    | .list (.atom id :: args) =>
      match id with
      | "fun" =>
        let [.list [.atom varId, .atom typeId], body] := args
          | throw s!"Unexpected fun: {t}"
        let body ← withReader (fun vars => vars.insert varId) do
          go body
        return .lam varId (.const typeId) body
      | "if" =>
        let [discr, t, e] := args
          | throw s!"Unexpected if: {t}"
        return .ite (← go discr) (← go t) (← go e)
      | "=" =>
        let [l, r] := args
          | throw s!"Unexpected equal: {t}"
        return .eq (← go l) (← go r)
      | id =>
        let base := if (← read).contains id then .var id else .const id
        return .appN base (← args.mapM go)
    | _ => throw s!"Unexpected term: {t}"

private def parse (d : Sexp) : Except String NunModelDecl := do
  match d with
  | .list [.atom "type", .atom id, .list members] =>
    let members ← members.mapM fun mem => do
      let .atom id := mem
        | throw s!"Unexpected type member: {mem}"
      return id
    return .type id members
  | .list [.atom "val", .atom id, value] =>
    let value ← parseTerm value
    return .val id value
  | _ => throw s!"Unexpected model decl: {d}"

instance : ToString NunModelDecl where
  toString decl := private
    match decl with
    | .type name members => s!"type {name} := [{String.intercalate " " members}]"
    | .val name term => s!"val {name} := {Std.ToFormat.format term}"

end NunModelDecl

structure NunModel where
  decls : List NunModelDecl

namespace NunModel

private def parse (m : List Sexp) : Except String NunModel := do
  let decls ← m.mapM NunModelDecl.parse
  return { decls }

instance : ToString NunModel where
  toString model := String.intercalate "\n" <| model.decls.map toString

end NunModel

abbrev NunResult := SolverResult NunModel

namespace NunResult

def parse (s : String) : Except String NunResult := do
  let s ← Sexp.parse s
  match s with
  | .list [.atom "SAT", .list model] =>
    let model ← NunModel.parse model
    return .sat model
  | .atom "UNSAT" => return .unsat
  | .atom "UNKNOWN" => return .unknown
  | _ => throw "Unexpected solver result"

end NunResult

abbrev LeanResult := SolverResult (List (Lean.Name × Lean.Expr))

namespace LeanResult

instance : Lean.ToMessageData LeanResult where
  toMessageData res :=
    -- TODO
    match res with
    | .unsat => "The prover is convinced that the theorem is true."
    | .unknown => "The prover wasn't able to prove or disprove the theorem."
    | .sat _ => "The prover found a counter example"

end LeanResult

end

end Nunchaku
