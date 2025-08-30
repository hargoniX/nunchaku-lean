import Nunchaku


/--
info: The prover found a counter example
---
error: unsolved goals
n m : Nat
⊢ n.add m = n.add n
---
trace: [nunchaku.equations] Collected equations:
[nunchaku.equations] - Nat.add
[nunchaku.equations]   - ∀ (x : Nat), x.add Nat.zero = x
[nunchaku.equations]   - ∀ (x b : Nat), x.add b.succ = (x.add b).succ
-/
#guard_msgs in
set_option trace.nunchaku.equations true in
example (n m : Nat) : n.add m = n.add n := by nunchaku
