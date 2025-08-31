import Nunchaku.Util.NunchakuSyntax

/-!
This module contains the implementation of the Nunchaku pretty printer, used to dump Nunchaku
problems to the external solver.
-/

namespace Nunchaku

open Std

private partial def NunType.format (typ : NunType) : Std.Format :=
  match typ with
  | .prop => "prop"
  | .type => "type"
  | .const name => name
  | .arrow lhs rhs => "(" ++ lhs.format ++ " -> " ++ rhs.format ++ ")"

instance : ToFormat NunType where
  format := NunType.format

private def NunTerm.format (term : NunTerm) : Std.Format :=
  match term with
  | .var id => idToVar id
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
    .paren (lhs.format ++ " <=> " ++ rhs.format)
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
    .paren ("fun (" ++ idToVar id ++ " : " ++ ToFormat.format ty ++ ") . " ++ body.format )
  | .forall id ty body =>
    .paren ("forall (" ++ idToVar id ++ " : " ++ ToFormat.format ty ++ ") . " ++ body.format )
  | .exists id ty body =>
    .paren ("exists (" ++ idToVar id ++ " : " ++ ToFormat.format ty ++ ") . " ++ body.format )
  | .let id value body =>
    .paren ("let " ++ idToVar id ++ " := " ++ value.format ++ " in " ++ .line ++ body.format)
where
  idToVar (id : Nat) : Format := s!"var{id}"

instance : ToFormat NunTerm where
  format := NunTerm.format

instance : ToFormat NunCtorSpec where
  format spec :=
    spec.arguments.foldl (init := .text spec.name) fun acc arg => acc ++ " " ++ ToFormat.format arg

instance : ToFormat NunDataSpec where
  format spec :=
    let firstCtor := ToFormat.format spec.ctors[0]!
    let ctors : Format := spec.ctors.tail.foldl (init := firstCtor) fun acc ctor =>
      acc ++ .line ++ "| " ++ ToFormat.format ctor
    spec.name ++ " := " ++ .nest 2 (.line ++ ctors)

instance : ToFormat NunPropSpec where
  format spec :=
    let firstLaw := ToFormat.format spec.laws[0]!
    let laws : Format := spec.laws.tail.foldl (init := firstLaw) fun acc law =>
      acc ++ ";" ++ .line ++ ToFormat.format law
    spec.name ++ " : " ++ ToFormat.format spec.type ++ " := " ++ .nest 2 (Format.line ++ laws)

instance : ToFormat NunCommand where
  format problem :=
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

instance : ToFormat NunProblem where
  format problem :=
    problem.commands.foldl (init := "") (fun init cmd => init ++ ToFormat.format cmd ++ .line)

instance : ToString NunProblem where
  toString problem := ToFormat.format problem |>.pretty

end Nunchaku
