/-
# ≤ World
-/

import Mathlib.Tactic.Use

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»
import «ℕGame».«ImplicationWorld»
import «ℕGame».«AdvancedAdditionWorld»

/--
## The `use` (`exists`) tactic
-/

theorem ℕ.leRefl (n: ℕ): n ≤ n := sorry

example (n: ℕ): n ≤ n := by
  exists 0
  rw [ℕ.add0]

/--
## 0 ≤ x
-/

theorem ℕ.zeroLe (n: ℕ): 0 ≤ n := sorry

example (n: ℕ): 0 ≤ n := by
  exists n
  rw [ℕ.add0L]

/--
## x ≤ succ x
-/

theorem ℕ.leSuccSelf (n: ℕ): n ≤ n.succ := sorry

example (n: ℕ): n ≤ n.succ := by
  exists 1
  rw [ℕ.succEqAddOne]

/--
## Transitivity
-/

theorem ℕ.leTrans (n₁ n₂ n₃: ℕ) (h₁: n₁ ≤ n₂) (h₂: n₂ ≤ n₃): n₁ ≤ n₃ := sorry

example (n₁ n₂ n₃: ℕ) (h₁: n₁ ≤ n₂) (h₂: n₂ ≤ n₃): n₁ ≤ n₃ := by
  sorry

/--
## x ≤ 0 → x = 0
-/

theorem ℕ.leZero (n: ℕ): n ≤ 0 → n = 0 := sorry

example (n: ℕ): n ≤ 0 → n = 0 := by
  intro h
  sorry
