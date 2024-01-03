/-
# ≤ World
-/

import Mathlib.Tactic.Use

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»
import «ℕGame».«ImplicationWorld»
import «ℕGame».«AdvancedAdditionWorld»

namespace Term
  /-
  ## The `use` (`exists`) tactic
  -/

  theorem leRefl (n: ℕ): n ≤ n :=
    have h: n + 0 = n := ℕ.add0 n
    ⟨0, Eq.symm h⟩

  /-
  ## 0 ≤ x
  -/

  theorem zeroLe (n: ℕ): 0 ≤ n :=
    have h: 0 + n = n := add0L n
    ⟨n, Eq.symm h⟩

  /-
  ## x ≤ succ x
  -/

  theorem leSuccSelf (n: ℕ): n ≤ n.succ :=
    have h: n.succ = n + 1 := succEqAddOne n
    ⟨1, h⟩

  /-
  ## Transitivity
  -/

  theorem leTrans (n₁ n₂ n₃: ℕ) (h₁: n₁ ≤ n₂) (h₂: n₂ ≤ n₃): n₁ ≤ n₃ := sorry

  /-
  ## x ≤ 0 → x = 0
  -/

  theorem leZero (n: ℕ): n ≤ 0 → n = 0 := sorry
end Term

namespace Tactic
  /-
  ## The `use` (`exists`) tactic
  -/

  @[local simp]
  theorem leRefl (n: ℕ): n ≤ n := by
    exists 0
    rw [ℕ.add0]

  /-
  ## 0 ≤ x
  -/

  @[local simp]
  theorem zeroLe (n: ℕ): 0 ≤ n := by
    exists n
    rw [add0L]

  /-
  ## x ≤ succ x
  -/

  @[local simp]
  theorem leSuccSelf (n: ℕ): n ≤ n.succ := by
    exists 1
    rw [succEqAddOne]

  /-
  ## Transitivity
  -/

  @[local simp]
  theorem leTrans (n₁ n₂ n₃: ℕ) (h₁: n₁ ≤ n₂) (h₂: n₂ ≤ n₃): n₁ ≤ n₃ := by
    sorry

  /-
  ## x ≤ 0 → x = 0
  -/

  @[local simp]
  theorem leZero (n: ℕ): n ≤ 0 → n = 0 := by
    intro h
    sorry
end Tactic

namespace Blended
  /-
  ## The `use` (`exists`) tactic
  -/

  @[local simp]
  theorem leRefl (n: ℕ): n ≤ n :=
    have h: n + 0 = n := by rw [ℕ.add0]
    ⟨0, Eq.symm h⟩

  /-
  ## 0 ≤ x
  -/

  @[local simp]
  theorem zeroLe (n: ℕ): 0 ≤ n :=
    have h: 0 + n = n := by rw [add0L]
    ⟨n, Eq.symm h⟩

  /-
  ## x ≤ succ x
  -/

  @[local simp]
  theorem leSuccSelf (n: ℕ): n ≤ n.succ :=
    have h: n.succ = n + 1 := by rw [succEqAddOne]
    ⟨1, h⟩

  /-
  ## Transitivity
  -/

  @[local simp]
  theorem leTrans (n₁ n₂ n₃: ℕ) (h₁: n₁ ≤ n₂) (h₂: n₂ ≤ n₃): n₁ ≤ n₃ := sorry

  /-
  ## x ≤ 0 → x = 0
  -/

  @[local simp]
  theorem leZero (n: ℕ): n ≤ 0 → n = 0 := sorry
end Blended
