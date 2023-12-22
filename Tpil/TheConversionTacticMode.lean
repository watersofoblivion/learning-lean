/-
# The Conversion Tactic Mode
-/

/-
## Basic Navigation and Rewriting
-/

example (a b c: Nat): a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    rfl
    rw [Nat.mul_comm]

example: (fun x: Nat => 0 + x) = (fun x: Nat => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]

example: (fun x: Nat => 0 + x) = (fun x: Nat => x) := by
  funext
  rw [Nat.zero_add]

example: (fun x: Nat => 0 + x) = (fun x: Nat => x) := by
  simp

/-
## Pattern Matching
-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c =>
    rw [Nat.mul_comm]

/-
## Structuring Conversion Tactics
-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    · rfl
    · rw [Nat.mul_comm]

/-
## Other Tactics Inside Conversion Mode
-/

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    arg 2
    rw [Nat.mul_comm]

def f (x: Nat) :=
  if x > 0
  then x + 1
  else x + 2

example (g: Nat → Nat) (h₁: g x = x + 1) (h₂: x > 0): g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁

example (g: Nat → Nat → Nat) (h₁: ∀ x: Nat, x ≠ 0 → g x x = 1) (h₂: x ≠ 0): g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    · skip
    . tactic => exact h₂

example (g: Nat → Nat → Nat) (h₁: ∀ x: Nat, x ≠ 0 → g x x = 1) (h₂: x ≠ 0): g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    · skip
    · apply h₂
