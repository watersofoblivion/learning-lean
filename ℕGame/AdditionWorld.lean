/-
# Addition World
-/

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»

/-- Level 1: Zero Add.  Explicitly uses `0`, not `ℕ.zero` -/
theorem ℕ.add0L (n: ℕ): 0 + n = n := by
  induction n with
    | zero =>
      rw [ℕ.addZero]
      rfl
    | succ n ihₙ => rw [ℕ.addSucc, ihₙ]

/-- Level 1: Zero Add.  Explicitly uses `ℕ.zero`, not `0`. -/
theorem ℕ.zeroAdd (n: ℕ): .zero + n = n := by
  induction n with
    | zero => rw [ℕ.addZero]
    | succ n ihₙ => rw [ℕ.addSucc, ihₙ]

/-- Level 2: Successor Add -/
theorem ℕ.succAdd (n₁ n₂: ℕ): succ n₁ + n₂ = succ (n₁ + n₂) := by
  induction n₂ with
    | zero => repeat rw [ℕ.addZero]
    | succ n₂ ihn₂ =>
      repeat rw [ℕ.addSucc]
      rw [ihn₂]

/-- Level 3: Add Commutivity -/
theorem ℕ.addComm (n₁ n₂: ℕ): n₁ + n₂ = n₂ + n₁ := by
  induction n₁ with
    | zero => rw [ℕ.addZero, ℕ.zeroAdd]
    | succ n₁ ihn₁ => rw [ℕ.addSucc, ℕ.succAdd, ihn₁]

/-- Level 4: Add Associativity -/
theorem ℕ.addAssoc (n₁ n₂ n₃: ℕ): n₁ + n₂ + n₃ = n₁ + (n₂ + n₃) := by
  induction n₁ with
    | zero => rw [ℕ.zeroAdd, ℕ.zeroAdd]
    | succ n₁ ihn₁ =>
      repeat rw [ℕ.succAdd]
      rw [ihn₁]

/-- Level 5: Add Right Commutivity -/
theorem ℕ.addRightComm (n₁ n₂ n₃: ℕ): n₁ + n₂ + n₃ = n₁ + n₃ + n₂ := by
  rw [ℕ.addAssoc, ℕ.addComm n₂ n₃, ← ℕ.addAssoc]
