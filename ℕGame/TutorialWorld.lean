/-
# Tutorial World
-/

import «ℕGame».«ℕ»

/-
## Levels
-/

/-- Level 1: The `rfl` tactic -/
example (x q: ℕ): 37 * x + q = 37 * x + q := by
  rfl

/-- Level 2: The `rw` tactic -/
example (x y: ℕ): y = x + 7 → 2 * y = 2 * (x + 7) := by
  intro h
  rw [h]

/-- Level 3: Two is the number after the number after zero, proven forward. -/
example: 2 = (0: ℕ).succ.succ := by
  rw [ℕ.twoSuccOfOne, ℕ.oneSuccOf0]

/-- Level 4: Two is the number after the number after zero, proven backwards. -/
example: 2 = (0: ℕ).succ.succ := by
  rw [← ℕ.oneSuccOf0, ← ℕ.twoSuccOfOne]

/-- Level 5: Adding zero -/
example (a b c: ℕ): a + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [ℕ.add0]

/-- Level 6: Precision Rewriting -/
example (a b c: ℕ): a + (b + 0) + (c + 0) = a + b + c := by
  rw [ℕ.add0 c, ℕ.add0 b]

/-- Level 7: Add Successor -/
theorem ℕ.succEqAddOne (n: ℕ): n.succ = n + 1 := by
  rw [ℕ.oneSuccOfZero, ℕ.addSucc, ℕ.addZero]

/-- Level 8: 2 + 2 = 4 -/
example: (2: ℕ) + 2 = 4 := by
  rw [ℕ.twoSuccOfOne, ℕ.oneSuccOfZero]
  rw [ℕ.fourSuccOfThree, ℕ.threeSuccOfTwo, ℕ.twoSuccOfOne, ℕ.oneSuccOfZero]
  repeat rw [ℕ.addSucc]
  rw [ℕ.addZero]
