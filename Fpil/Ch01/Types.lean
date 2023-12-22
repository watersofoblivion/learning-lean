/-
# 1.2 Types
-/

import Fpil.Abbrev

example: (1 + 2: ℕ) = (3: ℕ) := by rfl
example: 1 - 2 = 0 := by rfl
example: (1 - 2: ℤ) = -1 := by rfl

#check (1 - 2: ℤ)
