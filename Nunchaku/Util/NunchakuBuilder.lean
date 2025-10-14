module

public import Nunchaku.Util.NunchakuSyntax
public import Std.Data.HashSet.Basic

/-!
This module contains utility functions for building Nunchaku syntax and problems.
-/

namespace Nunchaku

public section

def NunType.ofList (types : List NunType) (h : types ≠ []) : NunType :=
  let revTypes := types.reverse
  let output := revTypes.head (by simp [h, revTypes])
  let remainder := revTypes.tail
  remainder.foldl (init := output) (fun acc typ => .arrow typ acc)

def NunTerm.not (arg : NunTerm) : NunTerm := .app (.builtin .not) arg
def NunTerm.and (lhs rhs : NunTerm) : NunTerm := .app (.app (.builtin .and) lhs) rhs
def NunTerm.or (lhs rhs : NunTerm) : NunTerm := .app (.app (.builtin .or) lhs) rhs
def NunTerm.eq (lhs rhs : NunTerm) : NunTerm := .app (.app (.builtin .eq) lhs) rhs
def NunTerm.neq (lhs rhs : NunTerm) : NunTerm := .app (.app (.builtin .neq) lhs) rhs
def NunTerm.equiv (lhs rhs : NunTerm) : NunTerm := .app (.app (.builtin .equiv) lhs) rhs
def NunTerm.imply (lhs rhs : NunTerm) : NunTerm := .app (.app (.builtin .imply) lhs) rhs
def NunTerm.ite (discr lhs rhs : NunTerm) : NunTerm :=
  .app (.app (.app (.builtin .ite) discr) lhs) rhs
def NunTerm.appN (fn : NunTerm) (args : List NunTerm) : NunTerm :=
  args.foldl (init := fn) .app

def NunType.collectUsedConstants (t : NunType) (s : Std.HashSet String := {}) :
    Std.HashSet String :=
  match t with
  | .prop | .type => s
  | .const name args =>
    let s := s.insert name
    args.foldl (init := s) (fun acc arg => arg.collectUsedConstants acc)
  | .arrow lhs rhs =>
    let s := lhs.collectUsedConstants s
    rhs.collectUsedConstants s

def NunTerm.collectUsedConstants (t : NunTerm) (s : Std.HashSet String := {}) :
    Std.HashSet String :=
  match t with
  | .var .. | .builtin .. => s
  | .const name => s.insert name
  | .lam _ ty body =>
    let s := ty.collectUsedConstants s
    body.collectUsedConstants s
  | .forall _ ty body =>
    let s := ty.collectUsedConstants s
    body.collectUsedConstants s
  | .exists _ ty body =>
    let s := ty.collectUsedConstants s
    body.collectUsedConstants s
  | .let _ value body =>
    let s := value.collectUsedConstants s
    body.collectUsedConstants s
  | .app fn arg =>
    let s := fn.collectUsedConstants s
    arg.collectUsedConstants s

end

end Nunchaku
