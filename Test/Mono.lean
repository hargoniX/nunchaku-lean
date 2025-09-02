import Nunchaku

set_option trace.nunchaku true in
example (xs : List α) : xs.map id ≠ xs := by
  nunchaku

set_option trace.nunchaku true in
example (xs : List (List α)) : xs.map id ≠ xs := by
  nunchaku

inductive Foo where
  | nil
  | cons (x : Nat) (xs : Foo)

def Foo.map (foo : Foo) (f : Nat → Nat) : Foo :=
  match foo with
  | .nil => .nil
  | .cons x xs => .cons (f x) (map xs f)

set_option trace.nunchaku true in
example (xs : Foo) : xs.map (fun x => x.succ) = xs := by
  nunchaku


set_option trace.nunchaku true in
example (xs : List Nat) (h : xs ≠ []) : xs.sum ≠ 0 := by
  nunchaku
