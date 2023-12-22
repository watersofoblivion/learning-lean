/-
# Implication World
-/

import Mathlib.Tactic.Relation.Symm

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»

/-- Level 1: The `exact` tactic -/
example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = 37) (_: 3 * n₁ + n₃ = 42): n₁ + n₂ = 37 := by
  exact h₁

/-- Level 2: `exact` practice -/
example (n₁: ℕ) (h: 0 + n₁ = 0 + n₂ + 2): n₁ = n₂ + 2 := by
  repeat rw [ℕ.add0L] at h
  exact h

/-- Level 3: The `apply` tactic -/
example (n₁ n₂: ℕ) (h₁: n₁ = 37) (h₂: n₁ = 37 → n₂ = 42): n₂ = 42 := by
  apply h₂ h₁

/-- Level 4: `succInj`: The successor function is injective -/
example (n: ℕ) (h: n + 1 = 4): n = 3 := by
  rw [ℕ.fourSuccOfThree, ← ℕ.succEqAddOne] at h
  apply ℕ.succInj -- at h -- at h -- Equivalent outside the NNG?
  exact h

/-- Level 5: Arguing backwards -/
example (n: ℕ) (h: n + 1 = 4): n = 3 := by
  apply ℕ.succInj
  rw [ℕ.succEqAddOne, ← ℕ.fourSuccOfThree]
  exact h

/-- Level 6: `intro` -/
example (n: ℕ): n = 37 → n = 37 := by
  intro h
  apply h

/-- Level 7: `intro` practice -/
example (n₁: ℕ): n₁ + 1 = n₂ + 1 → n₁ = n₂ := by
  intro h
  repeat rw [← ℕ.succEqAddOne] at h
  apply ℕ.succInj
  exact h

/-- Level 8: ≠ -/
example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False := by
  apply h₂ h₁

/-- Level 9: Zero ≠ Succ -/
theorem ℕ.zeroNeOne: (0: ℕ) ≠ 1 := by
  intro h
  rw [ℕ.oneSuccOfZero] at h
  apply ℕ.zeroNeSucc -- at h -- Equivalent outside the NNG?
  exact h

/-- Level 10: 1 ≠ 0 -/
theorem ℕ.oneNeZero: (1: ℕ) ≠ 0 := by
  symm
  exact ℕ.zeroNeOne

/-- Level 11: 2 + 2 ≠ 5 -/
example: (2: ℕ) + 2 ≠ 5 := by
  intro h
  repeat rw [ℕ.fiveSuccOfFour, ℕ.fourSuccOfThree, ℕ.threeSuccOfTwo, ℕ.twoSuccOfOne, ℕ.oneSuccOfZero] at h
  repeat rw [ℕ.addSucc] at h
  rw [ℕ.addZero] at h
  repeat rw [ℕ.zeroNeSucc] at h
  -- apply ℕ.succInj at h -- Equivalent outside the NNG?
  sorry
