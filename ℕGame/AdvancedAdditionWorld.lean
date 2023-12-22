/-
# Advanced Addition World
-/

import Mathlib.Tactic.Relation.Symm

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»
import «ℕGame».«ImplicationWorld»

/-- Level 1: n ≠ n.succ -/
theorem ℕ.neSuccSelf (n: ℕ): n ≠ n.succ := by
  induction n with
    | zero => apply ℕ.zeroNeSucc
    | succ n ihₙ =>
      intro h
      -- apply ℕ.succInj -- at h -- Eqivalent outside the NNG?
      -- apply ihₙ h
      -- exact h
      sorry

/-- Level 2: Add Right Cancel -/
theorem ℕ.addRightCancel (n₁ n₂ n₃: ℕ): n₁ + n₃ = n₂ + n₃ → n₁ = n₂ := by
  intro h
  induction n₃ with
    | zero =>
      rw [ℕ.addZero, ℕ.addZero] at h
      exact h
    | succ n₃ ihn₃ =>
      rw [ℕ.addSucc, ℕ.addSucc] at h
      -- apply ℕ.succInj -- at h -- Equivalent outside the NNG?
      -- apply ihn₃ -- at h -- Equivalent outside the NNG?
      -- exact h
      sorry

/-- Level 3: Add Left Cancel -/
theorem ℕ.addLeftCancel (n₁ n₂ n₃: ℕ): n₁ + n₂ = n₁ + n₃ → n₂ = n₃ := by
  repeat rw [ℕ.addComm n₁]
  exact ℕ.addRightCancel n₂ n₃ n₁

/-- Level 4: Add Left = Self -/
theorem ℕ.addLeftEqSelf (n₁ n₂: ℕ): n₁ + n₂ = n₂ → n₁ = 0 := by
  -- nth_rewrite 2 [←ℕ.zeroAdd n₂]
  intro h
  induction n₂ with
    | zero =>
      rw [ℕ.addZero] at h
      exact h
    | succ n₂ ihn₂ =>
      rw [ℕ.addSucc] at h
      -- apply ℕ.succInj -- at h -- Equivalent outside the NNG?
      -- apply ihn₂ h
      sorry

/-- Level 5: Add Right = Self -/
theorem ℕ.addRightEqSelf (n₁ n₂: ℕ): n₁ + n₂ = n₁ → n₂ = 0 := by
  rw [ℕ.addComm]
  exact ℕ.addLeftEqSelf n₂ n₁

/-- Level 6: a + b = 0 → a = 0 -/
theorem ℕ.eqZeroOfAddRightEqZero (n₁ n₂: ℕ): n₁ + n₂ = 0 → n₁ = 0 := by
  intro h
  cases n₂ with
    | zero =>
      rw [ℕ.addZero] at h
      exact h
    | succ n₂ =>
      -- tauto  -- Equivalent outside the NNG?
      sorry

/-- Level 7: a + b = 0 ⇒ b = 0 -/
theorem ℕ.eqZeroOfAddLeftEqZero (n₁ n₂: ℕ): n₁ + n₂ = 0 → n₂ = 0 := by
  rw [ℕ.addComm]
  apply ℕ.eqZeroOfAddRightEqZero
