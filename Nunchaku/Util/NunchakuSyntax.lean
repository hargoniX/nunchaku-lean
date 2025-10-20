module

/-!
This module contains the AST for Nunchaku problems. Note that the specific fragment of Nunchaku
we are targeting is already fully monomorphized so there is no need to account for things like
generic types.
-/

namespace Nunchaku

public section

inductive NunType where
  | prop
  | type
  | const (name : String) (args : List NunType)
  | arrow (lhs rhs : NunType)
  deriving Inhabited, Repr

/--
All Nunchaku built-in functions with special syntax, meaning etc.
-/
inductive NunBuiltin where
  /--
  If-then-else.
  -/
  | ite
  /--
  The asserting command.
  -/
  | asserting
  /--
  Logical not.
  -/
  | not
  /--
  Logical and.
  -/
  | and
  /--
  Logical or.
  -/
  | or
  /--
  Logical true.
  -/
  | true
  /--
  Logical false.
  -/
  | false
  /--
  Equality between values.
  -/
  | eq
  /--
  Disequality between values.
  -/
  | neq
  /--
  Equivalence between propositions.
  -/
  | equiv
  /--
  Logical implication.
  -/
  | imply
  deriving Inhabited, Repr

/--
A monomorphized Nunchaku term.
-/
inductive NunTerm where
  /--
  A variable, the identifier should be globally unique.
  -/
  | var (id : String)
  /--
  A Nunchaku constant such as a function.
  -/
  | const (name : String)
  /--
  A Nunchaku built-in.
  -/
  | builtin (builtin : NunBuiltin)
  /--
  A lambda abstraction `λ (id : ty) . body`
  -/
  | lam (id : String) (ty : NunType) (body : NunTerm)
  /--
  A forall abstraction `∀ (id : ty) . body`
  -/
  | forall (id : String) (ty : NunType) (body : NunTerm)
  /--
  An existential abstraction `∃ (id : ty) . body`
  -/
  | exists (id : String) (ty : NunType) (body : NunTerm)
  /--
  A let abstraction `let id := value in body`
  -/
  | let (id : String) (value : NunTerm) (body : NunTerm)
  /--
  A function application `fn arg`.
  -/
  | app (fn arg : NunTerm)
  deriving Inhabited, Repr

/--
A single `data` constructor declaration.
-/
structure NunCtorSpec where
  name : String
  arguments : List NunType
  deriving Inhabited, Repr

/--
A single `data` declaration, potentially within a mutual `data` block.
-/
structure NunDataSpec where
  name : String
  ctors : List NunCtorSpec
  deriving Inhabited, Repr

/--
A single `data` or `rec` declaration as a "propositional specification", potentially within a
mutual block.
-/
structure NunPropSpec where
  /--
  The name of the declaration.
  -/
  name : String
  /--
  The type of the object.
  -/
  type : NunType
  /--
  The laws associated with the declaration.
  -/
  laws : List NunTerm
  deriving Inhabited, Repr

/--
A monomorphized Nunchaku command.
-/
inductive NunCommand where
  /--
  `val name : type.`
  -/
  | valDecl (name : String) (typ : NunType)
  /--
  `data specs.`
  -/
  | dataDecl (specs : List NunDataSpec)
  /--
  `pred specs.`
  -/
  | predDecl (specs : List NunPropSpec)
  /--
  `rec specs.`
  -/
  | recDecl (specs : List NunPropSpec)
  /--
  `axiom type.`
  -/
  | axiomDecl (type : NunTerm)
  /--
  `goal type.`
  -/
  | goalDecl (type : NunTerm)
  deriving Inhabited, Repr

/--
A full Nunchaku problem.
-/
structure NunProblem where
  /--
  The commands of the Nunchaku problem.
  -/
  commands : List NunCommand
  deriving Inhabited, Repr

end

end Nunchaku
