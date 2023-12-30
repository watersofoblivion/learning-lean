/-
# Implication World
-/

import Mathlib.Tactic.Relation.Symm

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»

/--
## The `exact` tactic
-/

example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = 37) (_: 3 * n₁ + n₃ = 42): n₁ + n₂ = 37 := h₁

example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = 37) (_: 3 * n₁ + n₃ = 42): n₁ + n₂ = 37 := by
  exact h₁

/--
## `exact` practice
-/

example (n₁: ℕ) (h: 0 + n₁ = 0 + n₂ + 2): n₁ = n₂ + 2 :=
  have h₁: ℕ.add (0 + n₂) = ℕ.add n₂ := congrArg ℕ.add (ℕ.zeroAdd n₂)
  calc n₁
    _ = 0 + n₁     := Eq.symm (ℕ.zeroAdd n₁)
    _ = 0 + n₂ + 2 := h
    _ = n₂ + 2     := congrFun h₁ 2

example (n₁: ℕ) (h: 0 + n₁ = 0 + n₂ + 2): n₁ = n₂ + 2 := by
  repeat rw [ℕ.add0L] at h
  exact h

/--
## The `apply` tactic
-/

example (n₁ n₂: ℕ) (h₁: n₁ = 37) (h₂: n₁ = 37 → n₂ = 42): n₂ = 42 :=
  h₂ h₁

example (n₁ n₂: ℕ) (h₁: n₁ = 37) (h₂: n₁ = 37 → n₂ = 42): n₂ = 42 := by
  apply h₂ h₁

/--
## `succInj`: The successor function is injective
-/

example (n: ℕ) (h: n + 1 = 4): n = 3 :=
  have h₁: n.succ = (3: ℕ).succ :=
    calc n.succ
      _ = n + 1       := ℕ.succEqAddOne n
      _ = 4           := h
      _ = (3: ℕ).succ := ℕ.fourSuccOfThree
  ℕ.succInj n 3 h₁

example (n: ℕ) (h: n + 1 = 4): n = 3 := by
  rw [ℕ.fourSuccOfThree, ← ℕ.succEqAddOne] at h
  apply ℕ.succInj
  exact h

/--
## Arguing backwards
-/

-- example (n: ℕ) (h: n + 1 = 4): n = 3 := sorry

example (n: ℕ) (h: n + 1 = 4): n = 3 := by
  apply ℕ.succInj
  rw [ℕ.succEqAddOne, ← ℕ.fourSuccOfThree]
  exact h

/--
## `intro`
-/

example (n: ℕ): n = 37 → n = 37
  | h => h

example (n: ℕ): n = 37 → n = 37 := by
  intro h
  apply h

/--
## `intro` practice
-/

example (n₁: ℕ) (h: n₁ + 1 = n₂ + 1): n₁ = n₂ :=
  have h₁: n₁.succ = n₂.succ :=
    calc n₁.succ
      _ = n₁ + 1 := ℕ.succEqAddOne n₁
      _ = n₂ + 1 := h
      _ = n₂.succ := Eq.symm (ℕ.succEqAddOne n₂)
  ℕ.succInj n₁ n₂ h₁

example (n₁: ℕ): n₁ + 1 = n₂ + 1 → n₁ = n₂ := by
  intro h
  repeat rw [← ℕ.succEqAddOne] at h
  apply ℕ.succInj
  exact h

/--
## ≠
-/

example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False :=
  absurd h₁ h₂

example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False := by
  apply h₂ h₁

example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False := by
  contradiction

/--
## Zero ≠ Succ
-/

theorem ℕ.zeroNeOne: (0: ℕ) ≠ 1
  | h => absurd h (ℕ.zeroNeSucc ℕ.zero)

example: (0: ℕ) ≠ 1 := by
  intro h
  rw [ℕ.oneSuccOfZero] at h
  apply ℕ.zeroNeSucc -- at h -- Equivalent outside the NNG?
  exact h

/--
## 1 ≠ 0
-/

theorem ℕ.oneNeZero: (1: ℕ) ≠ 0
  | h => ℕ.zeroNeOne (Eq.symm h)

example: (1: ℕ) ≠ 0 := by
  symm
  exact ℕ.zeroNeOne

/--
## 2 + 2 ≠ 5
-/

example: (2: ℕ) + 2 ≠ 5
  | h => sorry

example: (2: ℕ) + 2 ≠ 5 := by
  intro h
  repeat rw [ℕ.fiveSuccOfFour, ℕ.fourSuccOfThree, ℕ.threeSuccOfTwo, ℕ.twoSuccOfOne, ℕ.oneSuccOfZero] at h
  repeat rw [ℕ.addSucc] at h
  rw [ℕ.addZero] at h
  repeat rw [ℕ.zeroNeSucc] at h
  -- apply ℕ.succInj at h -- Equivalent outside the NNG?
  sorry
