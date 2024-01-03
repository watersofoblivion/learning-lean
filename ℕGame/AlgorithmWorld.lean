/-
# Algorithm World
-/

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»
import «ℕGame».«ImplicationWorld»
import «ℕGame».«AdvancedAdditionWorld»

namespace Term
  /-
  ## Add Left Commutative
  -/

  theorem addLeftComm: ∀ n₁ n₂ n₃: ℕ, n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) := sorry

  /-
  ## Making Life Easier
  -/

  example: ∀ n₁ n₂ n₃ n₄: ℕ, n₁ + n₂ + (n₃ + n₄) = n₁ + n₃ + n₄ + n₂ := sorry

  /-
  ## Making Life Simple
  -/

  example: ∀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈: ℕ, (n₄ + n₆) + (n₈ + (n₁ + n₃)) + (n₇ + n₅ + n₂) = n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ := sorry

  /-
  ## The Simplest Approach
  -/

  example: ∀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈: ℕ, (n₄ + n₆) + (n₈ + (n₁ + n₃)) + (n₇ + n₅ + n₂) = n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ := sorry

  /-
  ## Predecessor
  -/

  example: ∀ n₁ n₂: ℕ, n₁.succ = n₂.succ → n₁ = n₂ := sorry

  /-
  ## Successor Not Equal to Zero
  -/

  theorem succNeZero: ∀ n: ℕ, n.succ ≠ 0 := sorry

  /-
  ## Successor Not Equal to Successor
  -/

  theorem succNeSucc: ∀ n₁ n₂: ℕ, n₁ ≠ n₂ → n₁.succ ≠ n₂.succ := sorry

  /-
  ## Decide
  -/

  example: (20: ℕ) + 20 = 40 := sorry

  /-
  ## Decide, Again
  -/

  example: 2 + 2 ≠ 5 := sorry
end Term

namespace Tactic
  /-
  ## Add Left Commutative
  -/

  @[local simp]
  theorem addLeftComm: ∀ n₁ n₂ n₃: ℕ, n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) := by
    sorry

  /-
  ## Making Life Easier
  -/

  example: ∀ n₁ n₂ n₃ n₄: ℕ, n₁ + n₂ + (n₃ + n₄) = n₁ + n₃ + n₄ + n₂ := by
    sorry

  /-
  ## Making Life Simple
  -/

  example: ∀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈: ℕ, (n₄ + n₆) + (n₈ + (n₁ + n₃)) + (n₇ + n₅ + n₂) = n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ := by
    sorry

  /-
  ## The Simplest Approach
  -/

  example: ∀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈: ℕ, (n₄ + n₆) + (n₈ + (n₁ + n₃)) + (n₇ + n₅ + n₂) = n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ := by
    sorry

  /-
  ## Predecessor
  -/

  example: ∀ n₁ n₂: ℕ, n₁.succ = n₂.succ → n₁ = n₂ := by
    sorry

  /-
  ## Successor Not Equal to Zero
  -/

  @[local simp]
  theorem succNeZero: ∀ n: ℕ, n.succ ≠ 0 := by
    sorry

  /-
  ## Successor Not Equal to Successor
  -/

  @[local simp]
  theorem succNeSucc: ∀ n₁ n₂: ℕ, n₁ ≠ n₂ → n₁.succ ≠ n₂.succ := by
    sorry

  /-
  ## Decide
  -/

  example: (20: ℕ) + 20 = 40 := by
    sorry

  /-
  ## Decide, Again
  -/

  example: 2 + 2 ≠ 5 := by
    sorry
end Tactic

namespace Blended
  /-
  ## Add Left Commutative
  -/

  @[local simp]
  theorem addLeftComm: ∀ n₁ n₂ n₃: ℕ, n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) := sorry

  /-
  ## Making Life Easier
  -/

  example: ∀ n₁ n₂ n₃ n₄: ℕ, n₁ + n₂ + (n₃ + n₄) = n₁ + n₃ + n₄ + n₂ := sorry

  /-
  ## Making Life Simple
  -/

  example: ∀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈: ℕ, (n₄ + n₆) + (n₈ + (n₁ + n₃)) + (n₇ + n₅ + n₂) = n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ := sorry

  /-
  ## The Simplest Approach
  -/

  example: ∀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈: ℕ, (n₄ + n₆) + (n₈ + (n₁ + n₃)) + (n₇ + n₅ + n₂) = n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ + n₈ := sorry

  /-
  ## Predecessor
  -/

  example: ∀ n₁ n₂: ℕ, n₁.succ = n₂.succ → n₁ = n₂ := sorry

  /-
  ## Successor Not Equal to Zero
  -/

  @[local simp]
  theorem succNeZero: ∀ n: ℕ, n.succ ≠ 0 := sorry

  /-
  ## Successor Not Equal to Successor
  -/

  @[local simp]
  theorem succNeSucc: ∀ n₁ n₂: ℕ, n₁ ≠ n₂ → n₁.succ ≠ n₂.succ := sorry

  /-
  ## Decide
  -/

  example: (20: ℕ) + 20 = 40 := sorry

  /-
  ## Decide, Again
  -/

  example: 2 + 2 ≠ 5 := sorry
end Blended
