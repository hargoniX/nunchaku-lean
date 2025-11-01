module

public import Lean.Expr
public import Lean.Message
public import Chako.Util.Sexp
public import Chako.Util.NunchakuSyntax
import Chako.Util.NunchakuBuilder
import Chako.Util.NunchakuPrinter
import Std.Data.TreeSet.Basic

/-!
This module contains the definition of a Chako result, including the kind of models
nunchaku is capable of returning.
-/

namespace Chako

public section

inductive SolverResult (α : Type) where
  | unsat
  | unknown
  | sat (x : α)

namespace SolverResult

def map (f : α → β) (res : SolverResult α) : SolverResult β :=
  match res with
  | .unsat => .unsat
  | .unknown => .unknown
  | .sat x => .sat <| f x

def mapM [Monad m] (f : α → m β) (res : SolverResult α) : m (SolverResult β) := do
  match res with
  | .unsat => return .unsat
  | .unknown => return .unknown
  | .sat x => return .sat (← f x)

end SolverResult

inductive NunModelDecl where
  | type (name : String) (members : List String)
  | val (name : String) (value : NunTerm)
  | witness (name : String) (value : NunTerm)

namespace NunModelDecl

def name : NunModelDecl → String
  | .type name .. | .val name .. | .witness name .. => name

private def parseType (ty : Sexp) : Except String NunType := do
  match ty with
  | .atom "prop" => return .prop
  | .atom "type" => return .type
  | .atom id => return .const id []
  | .list [.atom "->", lhs, rhs] =>
    return .arrow (← parseType lhs) (← parseType rhs)
  | _ => throw s!"Unexpected type: {ty}"

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
        match args with
        -- Two formats for some reason
        | [.list [.atom varId, ty], body] =>
          let body ← withReader (fun vars => vars.insert varId) do
            go body
          return .lam [(varId, (← parseType ty))] body
        | [.list binders, body] =>
          let binders ← binders.mapM
            fun
              | .list [.atom varId, ty] => do return (varId, (← parseType ty))
              | _ => throw s!"Unexpected fun: {t}"
          let newVars := binders.map Prod.fst
          let body ← withReader (fun vars => vars.insertMany newVars) do
            go body
          return .lam binders body
        | _ => throw s!"Unexpected fun: {t}"
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
  | .list [.atom "val", .list [.atom "_witness_of", _], value] =>
    let value ← parseTerm value
    return .witness "_witness_of" value
  | _ => throw s!"Unexpected model decl: {d}"

instance : ToString NunModelDecl where
  toString decl := private
    match decl with
    | .type name members =>
      let members := members.map (s!" | {·}") |> String.join
      s!"inductive {name} where{members}"
    | .val name term => s!"val {name} := {Std.ToFormat.format term}"
    | .witness name value => s!"witness {name} := {Std.ToFormat.format value}"

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

instance : Lean.ToMessageData NunResult where
  toMessageData res :=
    -- TODO
    match res with
    | .unsat => "Chako is convinced that the theorem is true."
    | .unknown => "Chako wasn't able to prove or disprove the theorem."
    | .sat model => m!"Chako found a counter example:\n{model}"

end NunResult


end

end Chako
