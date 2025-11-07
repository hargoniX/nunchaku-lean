import Chako

@[specialize]
def binSearchAux {α : Type u} (lt : α → α → Bool) (as : Array α) (k : α) (lo : Fin (as.size + 1))
    (hi : Fin as.size) (h : lo.1 ≤ hi.1) : Option α :=
  let m := (lo.1 + hi.1) / 2
  let a := as[m]
  if lt a k then
    if h' : m + 1 ≤ hi.1 then
      binSearchAux lt as k ⟨m + 1, by grind⟩ hi h'
    else
      none
  else if lt k a then
    if h' : m = 0 ∨ m - 1 < lo.1 then
      none
    else
      binSearchAux lt as k lo ⟨m - 1, by grind⟩ (by grind)
  else
    (some a)
termination_by hi.1 - lo.1

#print binSearchAux
set_option pp.fieldNotation false in
#print binSearchAux._unary

def binSearch {α : Type u} (as : Array α) (k : α) (lt : α → α → Bool) : Option α :=
  let lo := 0
  let hi := as.size - 1
  if h : lo < as.size then
    binSearchAux lt as k ⟨lo, by grind⟩ ⟨hi, by grind⟩ (by grind)
  else
    none

/- Lacks (h : xs.Sorted Nat.blt) -/
theorem complete (xs : Array Nat) (h : n ∈ xs) : xs.binSearch n Nat.blt = some n := by
  chako

/- Is an → not a ↔ -/
theorem sound (xs : Array Nat) : xs.binSearch n Nat.blt = some y ↔ n = y := by
  chako
