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
example (α : Type) (xs : MList α) (f : α → α) : xs.map f ≠ xs := by
  nunchaku

end Foo

set_option trace.nunchaku true in
example  : [].map id ≠ ([] : List Nat) := by
  nunchaku

set_option trace.nunchaku true in
example (xs : List a) : xs = [] := by
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
  List.foldr Nat.add .zero

set_option trace.nunchaku true in
example (xs : List Nat) (h : xs ≠ []) : sumalt xs ≠ .zero := by
  nunchaku

def sumalt' : List Nat → Nat :=
  List.foldr (· + ·) .zero

set_option trace.nunchaku true in
example (x y : Nat) : x + y ≠ x := by
  nunchaku

set_option trace.nunchaku true in
example (xs : List Nat) (h : xs ≠ []) : sumalt' xs ≠ .zero := by
  nunchaku

def foo (xs : List α) : List α := id xs

set_option trace.nunchaku true in
example (xs : List α) : foo xs = id xs := by
  nunchaku

example (xs : List α) (h : xs = []) : xs.all f = false := by
  nunchaku

inductive MyAll {α : Type} (p : α → Prop) : List α → Prop where
  | nil : MyAll p []
  | cons (x : α) (xs : List α) (h1 : p x) (h2 : MyAll p xs) : MyAll p (x :: xs)

-- TODO: probably nunchaku bug
set_option trace.nunchaku true in
example (xs : List α) (h : xs = []) : MyAll (fun _ => False) xs := by
  nunchaku
