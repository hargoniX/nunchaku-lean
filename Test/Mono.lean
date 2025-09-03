import Nunchaku

set_option trace.nunchaku true in
example (xs : List α) : xs.map id ≠ xs := by
  nunchaku

set_option trace.nunchaku true in
example (xs : List (List α)) : xs.map id ≠ xs := by
  nunchaku

set_option trace.nunchaku true in
example (xs : List (List α)) : xs.map (·.map id) ≠ xs := by
  nunchaku


def sumalt : List Nat → Nat :=
  List.foldr (· + ·) .zero

set_option trace.nunchaku true in
example (xs : List Nat) (h : xs ≠ []) : sumalt xs ≠ .zero := by
  nunchaku

set_option trace.nunchaku true in
example (xs : List Nat) (h : xs ≠ []) : xs.sum ≠ .zero := by
  nunchaku
