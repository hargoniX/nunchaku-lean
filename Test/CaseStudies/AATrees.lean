import Chako

inductive AATree (α : Type u) where
  | nil
  | node (x : α) (level : Nat) (l r : AATree α)
  deriving Repr

namespace AATree

def lvl : AATree α → Nat
  | nil => 0
  | node _ lvl _ _ => lvl

def left : AATree α → AATree α
  | nil => .nil
  | node _ _ l _ => l

def right : AATree α → AATree α
  | nil => .nil
  | node _ _ _ r => r

def isNil : AATree α → Bool
  | nil => true
  | node .. => false

def data (t : AATree α) (h : t.isNil = false := by grind) : α :=
  match t with
  | nil => False.elim (by grind [isNil])
  | node x .. => x

def mem (x : α) : AATree α → Prop
  | nil => False
  | node d _ l r => d = x ∨ mem x l ∨ mem x r

def WF : AATree α → Prop
  | nil => True
  | node _ lvl nil nil => lvl = 1
  | node _ lvl l r =>
    WF l ∧ WF r ∧ lvl ≥ r.lvl ∧ lvl > l.lvl ∧ (lvl > 1 → (!l.isNil ∧ !r.isNil))

def skew : AATree α → AATree α
  | nil => nil
  | node x lvl l r =>
    -- TODO: typo l to r here
    if h : !l.isNil ∧ lvl = l.lvl then
      node l.data lvl l.left (node x lvl l.right r)
    else
      node x lvl l r

def split : AATree α → AATree α
  | nil => nil
  | node x lvl l r =>
    if h : !r.isNil ∧ lvl = r.right.lvl then
      node r.data (lvl + 1) (node x lvl l r.left) r.right
    else
      node x lvl l r

def insert [LT α] [DecidableLT α] (t : AATree α) (x : α) : AATree α :=
  match t with
  | nil => .node x 1 nil nil
  | node y lvl l r =>
    let l' := if x < y then l.insert x else l
    let r' := if x > y then r.insert x else r
    split <| skew <| node y lvl l' r'


section

variable {α : Type u} (t : AATree α)

example : mem x t ↔ t.skew.mem x := by
  chako

example : mem x t ↔ t.split.mem x := by
  chako

example : WF t → t.skew = t := by
  sorry
  -- timeout chako

example : WF t → t.split = t := by
  sorry
  -- timeout chako

end

#eval insert (AATree.node (Nat.succ Nat.zero) (Nat.succ Nat.zero) AATree.nil AATree.nil) 0
example (t : AATree Nat) : WF t → WF (t.insert x) := by
  sorry
  -- timeout chako
