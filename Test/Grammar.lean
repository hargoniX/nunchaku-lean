import Chako

/-!
The following example is taken from https://www.tcs.ifi.lmu.de/staff/jasmin-blanchette/sqj2013-relational.pdf
section 7.1.
-/

inductive Alphabet where
  | a
  | b

def Alphabet.beq : Alphabet → Alphabet → Bool
    | .a, .a => true
    | .b, .b => true
    | .a, .b => false
    | .b, .a => false

instance foo : BEq Alphabet where
  beq := Alphabet.beq

/-!
This is an erroneous version of the grammar
S := ε | bA | aB
A := aS | bAA
B := bS | aBB
-/

mutual

inductive S : List Alphabet → Prop where
  | nil : S []
  | a (h : A w) : S (.b :: w)
  | b (h : B w) : S (.a :: w)
  | step (h : S w) : S (.b :: w)

inductive A : List Alphabet → Prop where
  | s (h : S w) : A (.a :: w)

inductive B : List Alphabet → Prop where
  | step (h1 : B v) (h2 : B v) : B ((.a :: v) ++ w)

end

def count (x : Alphabet) (xs : List Alphabet) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => (if x == y then 1 else 0) + count x ys

/-
TODO: this is going to work with the predicate optimization
TODO: re-evaluate with bultin count then

set_option trace.chako true in
theorem sound (h : S w) : count .a w = count .b w := by
  chako
-/

/-
TODO: this doesn't work at all :(

theorem complete (w : List Alphabet) (h : count .a w = count .b w) : S w := by
  chako
-/
