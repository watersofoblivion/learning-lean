/-
# ≤ World
-/

import Mathlib.Tactic.Use

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»
import «ℕGame».«ImplicationWorld»
import «ℕGame».«AdvancedAdditionWorld»

/-- Level 1: The `use` (`exists`) tactic -/
theorem ℕ.leRefl (n: ℕ): n ≤ n := by
  exists 0
  rw [ℕ.add0]

/-- Level 2: 0 ≤ x -/
theorem ℕ.zeroLe (n: ℕ): 0 ≤ n := by
  exists n
  rw [ℕ.add0L]

/-- Level 3: x ≤ succ x -/
theorem ℕ.leSuccSelf (n: ℕ): n ≤ n.succ := by
  exists 1
  rw [ℕ.succEqAddOne]

/-- Level 4: Transitivity -/
theorem ℕ.leTrans (n₁ n₂ n₃: ℕ) (h₁: n₁ ≤ n₂) (h₂: n₂ ≤ n₃): n₁ ≤ n₃ := by
  sorry

/-- Level 5: x ≤ 0 → x = 0 -/
theorem ℕ.leZero (n: ℕ): n ≤ 0 → n = 0 := by
  intro h
  sorry
