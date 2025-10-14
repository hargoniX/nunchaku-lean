module

public import Nunchaku.Util.NunchakuSyntax

/-!
This module contains the implementation of the Nunchaku pretty printer, used to dump Nunchaku
problems to the external solver.
-/

namespace Nunchaku

open Std

partial def NunType.format (typ : NunType) : Std.Format :=
  match typ with
  | .prop => "prop"
  | .type => "type"
  | .const name [] => name
  | .const name args =>
    let args := args.map NunType.format
    let args := Format.joinSep args " "
    "(" ++ name ++ " " ++ args ++ ")"
  | .arrow lhs rhs => "(" ++ lhs.format ++ " -> " ++ rhs.format ++ ")"

public instance : ToFormat NunType where
  format := private NunType.format

def NunTerm.format (term : NunTerm) : Std.Format :=
  match term with
  | .var id => id
  | .const name => name
  | .builtin .true => "true"
  | .builtin .false => "false"
  | .builtin _ => panic! "encountered partially applied built-in in 0-ary position"
  | .app (.builtin .not) arg => .paren ("~ " ++ arg.format)
  | .app (.builtin _) _  => panic! "encountered partially applied built-in in 1-ary position"
  | .app (.app (.builtin .asserting) lhs) rhs =>
    .paren (lhs.format ++ " asserting " ++ rhs.format)
  | .app (.app (.builtin .and) lhs) rhs =>
    .paren (lhs.format ++ " && " ++ rhs.format)
  | .app (.app (.builtin .or) lhs) rhs =>
    .paren (lhs.format ++ " || " ++ rhs.format)
  | .app (.app (.builtin .eq) lhs) rhs =>
    .paren (lhs.format ++ " = " ++ rhs.format)
  | .app (.app (.builtin .neq) lhs) rhs =>
    .paren (lhs.format ++ " != " ++ rhs.format)
  | .app (.app (.builtin .equiv) lhs) rhs =>
    .paren (lhs.format ++ " = " ++ rhs.format)
  | .app (.app (.builtin .imply) lhs) rhs =>
    .paren (lhs.format ++ " => " ++ rhs.format)
  | .app (.app (.builtin _) _) _ =>
    panic! "encountered partially applied built-in in 2-ary position"
  | .app (.app (.app (.builtin .ite) discr) lhs) rhs =>
    .paren ("if " ++ discr.format ++ " then " ++ lhs.format ++ " else " ++ rhs.format)
  | .app (.app (.app (.builtin _) _) _) _ =>
    panic! "encountered partially applied built-in in 3-ary position"
  | .app fn arg => .paren (fn.format ++ " " ++ arg.format)
  | .lam id ty body =>
    .paren ("fun (" ++ id ++ " : " ++ ToFormat.format ty ++ ") . " ++ body.format )
  | .forall id ty body =>
    .paren ("forall (" ++ id ++ " : " ++ ToFormat.format ty ++ ") . " ++ body.format )
  | .exists id ty body =>
    .paren ("exists (" ++ id ++ " : " ++ ToFormat.format ty ++ ") . " ++ body.format )
  | .let id value body =>
    .paren ("let " ++ id ++ " := " ++ value.format ++ " in " ++ .line ++ body.format)

public instance : ToFormat NunTerm where
  format := private NunTerm.format

public instance : ToFormat NunCtorSpec where
  format spec := private
    spec.arguments.foldl (init := .text spec.name) fun acc arg => acc ++ " " ++ ToFormat.format arg

public instance : ToFormat NunDataSpec where
  format spec := private
    let firstCtor := ToFormat.format spec.ctors[0]!
    let ctors : Format := spec.ctors.tail.foldl (init := firstCtor) fun acc ctor =>
      acc ++ .line ++ "| " ++ ToFormat.format ctor
    spec.name ++ " :=" ++ .nest 2 (.line ++ ctors)

public instance : ToFormat NunPropSpec where
  format spec := private
    let firstLaw := ToFormat.format spec.laws[0]!
    let laws : Format := spec.laws.tail.foldl (init := firstLaw) fun acc law =>
      acc ++ ";" ++ .line ++ ToFormat.format law
    spec.name ++ " : " ++ ToFormat.format spec.type ++ " :=" ++ .nest 2 (Format.line ++ laws)

public instance : ToFormat NunCommand where
  format problem := private
    match problem with
    | .valDecl name typ => s!"val {name} : " ++ ToFormat.format typ ++ "."
    | .dataDecl specs =>
      let first := ToFormat.format specs[0]!
      let combined := specs.tail.foldl (init := first) fun acc spec =>
        let fmt := ToFormat.format spec
        acc ++ .line ++ "and " ++ fmt
      "data " ++ combined ++ "."
    | .predDecl specs =>
      let first := ToFormat.format specs[0]!
      let combined := specs.tail.foldl (init := first) fun acc spec =>
        let fmt := ToFormat.format spec
        acc ++ .line ++ "and " ++ fmt
      "pred " ++ combined ++ "."
    | .recDecl specs =>
      let first := ToFormat.format specs[0]!
      let combined := specs.tail.foldl (init := first) fun acc spec =>
        let fmt := ToFormat.format spec
        acc ++ .line ++ "and " ++ fmt
      "rec " ++ combined ++ "."
    | .axiomDecl type => "axiom " ++ ToFormat.format type ++ "."
    | .goalDecl type => "goal " ++ ToFormat.format type ++ "."

public instance : ToFormat NunProblem where
  format problem := private
    problem.commands.foldl (init := "") (fun init cmd => init ++ ToFormat.format cmd ++ .line)

public instance : ToString NunProblem where
  toString problem := private
    ToFormat.format problem |>.pretty

end Nunchaku
