import Nunchaku

namespace Foo

inductive MList (α : Type) where
  | nil
  | cons (x : α) (xs : MList α)

def MList.map (xs : MList α) (f : α → β) : MList β :=
  match xs with
  | .nil => .nil
  | .cons x xs => .cons (f x) (map xs f)

set_option trace.nunchaku true in
example  : MList.nil.map Nat.succ ≠ (.nil : MList Nat) := by
  nunchaku

end Foo

set_option trace.nunchaku true in
example  : [].map id ≠ ([] : List Nat) := by
  nunchaku

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

set_option trace.nunchaku true in
example (xs : List (Fin n)) : xs.map id ≠ xs := by
  nunchaku

set_option trace.nunchaku true in
example (xs : List (Fin .zero)) : ¬ xs.isEmpty := by
  nunchaku
