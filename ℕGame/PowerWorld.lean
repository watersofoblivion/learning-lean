/-
# Power World
-/

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»
import «ℕGame».«MultiplicationWorld»

namespace Term
  /-
  ## Zero to the Zero
  -/

  theorem zeroPowZero: (0: ℕ) ^ 0 = 1 := sorry

  /-
  ## Zero to a Successor
  -/

  theorem zeroPowSucc: ∀ n: ℕ, (0: ℕ) ^ n.succ = 0 := sorry

  /-
  ## ℕ to the 1
  -/

  theorem powOne: ∀ n: ℕ, n ^ (1: ℕ) = n := sorry

  /-
  ## 1 to the ℕ
  -/

  theorem onePow: ∀ n: ℕ, (1: ℕ) ^ n = 1 := sorry

  /-
  ## ℕ squared
  -/

  theorem powTwo: ∀ n: ℕ, n ^ 2 = n * n := sorry

  /-
  ## Power of a Sum
  -/

  theorem powAdd: ∀ x n₁ n₂: ℕ, x ^ (n₁ + n₂) = x ^ n₁ * x ^ n₂ := sorry

  /-
  ## Exponentiation Distributes over Multiplication
  -/

  theorem mulPow: ∀ n₁ n₂ x: ℕ, (n₁ * n₂) ^ x = n₁ ^ x * n₂ ^ x := sorry

  /-
  ## Power of a Power
  -/

  theorem powPow: ∀ x n₁ n₂: ℕ, (x ^ n₂) ^ n₃ = x ^ (n₂ * n₃) := sorry

  /-
  ## Square of Addition
  -/

  theorem addSq: ∀ n₁ n₂: ℕ, (n₁ + n₂) ^ 2 = n₁ ^ 2 + n₂ ^ 2 + 2 * n₁ * n₂ := sorry

  /-
  ## Fermat's Last Theorem
  -/

  example (a b c n: ℕ): (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := sorry
end Term

namespace Tactic
  /-
  ## Zero to the Zero
  -/

  @[local simp]
  theorem zeroPowZero: (0: ℕ) ^ 0 = 1 := by
    sorry

  /-
  ## Zero to a Successor
  -/

  @[local simp]
  theorem zeroPowSucc: ∀ n: ℕ, (0: ℕ) ^ n.succ = 0 := by
    sorry

  /-
  ## ℕ to the 1
  -/

  @[local simp]
  theorem powOne: ∀ n: ℕ, n ^ (1: ℕ) = n := by
    sorry

  /-
  ## 1 to the ℕ
  -/

  @[local simp]
  theorem onePow: ∀ n: ℕ, (1: ℕ) ^ n = 1 := by
    sorry

  /-
  ## ℕ squared
  -/

  @[local simp]
  theorem powTwo: ∀ n: ℕ, n ^ 2 = n * n := by
    sorry

  /-
  ## Power of a Sum
  -/

  @[local simp]
  theorem powAdd: ∀ x n₁ n₂: ℕ, x ^ (n₁ + n₂) = x ^ n₁ * x ^ n₂ := by
    sorry

  /-
  ## Exponentiation Distributes over Multiplication
  -/

  @[local simp]
  theorem mulPow: ∀ n₁ n₂ x: ℕ, (n₁ * n₂) ^ x = n₁ ^ x * n₂ ^ x := by
    sorry

  /-
  ## Power of a Power
  -/

  @[local simp]
  theorem powPow: ∀ x n₁ n₂: ℕ, (x ^ n₂) ^ n₃ = x ^ (n₂ * n₃) := by
    sorry

  /-
  ## Square of Addition
  -/

  @[local simp]
  theorem addSq: ∀ n₁ n₂: ℕ, (n₁ + n₂) ^ 2 = n₁ ^ 2 + n₂ ^ 2 + 2 * n₁ * n₂ := by
    sorry

  /-
  ## Fermat's Last Theorem
  -/

  example (a b c n: ℕ): (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
    sorry
end Tactic

namespace Blended
  /-
  ## Zero to the Zero
  -/

  @[local simp]
  theorem zeroPowZero: (0: ℕ) ^ 0 = 1 := sorry

  /-
  ## Zero to a Successor
  -/

  @[local simp]
  theorem zeroPowSucc: ∀ n: ℕ, (0: ℕ) ^ n.succ = 0 := sorry

  /-
  ## ℕ to the 1
  -/

  @[local simp]
  theorem powOne: ∀ n: ℕ, n ^ (1: ℕ) = n := sorry

  /-
  ## 1 to the ℕ
  -/

  @[local simp]
  theorem onePow: ∀ n: ℕ, (1: ℕ) ^ n = 1 := sorry

  /-
  ## ℕ squared
  -/

  @[local simp]
  theorem powTwo: ∀ n: ℕ, n ^ 2 = n * n := sorry

  /-
  ## Power of a Sum
  -/

  @[local simp]
  theorem powAdd: ∀ x n₁ n₂: ℕ, x ^ (n₁ + n₂) = x ^ n₁ * x ^ n₂ := sorry

  /-
  ## Exponentiation Distributes over Multiplication
  -/

  @[local simp]
  theorem mulPow: ∀ n₁ n₂ x: ℕ, (n₁ * n₂) ^ x = n₁ ^ x * n₂ ^ x := sorry

  /-
  ## Power of a Power
  -/

  @[local simp]
  theorem powPow: ∀ x n₁ n₂: ℕ, (x ^ n₂) ^ n₃ = x ^ (n₂ * n₃) := sorry

  /-
  ## Square of Addition
  -/

  @[local simp]
  theorem addSq: ∀ n₁ n₂: ℕ, (n₁ + n₂) ^ 2 = n₁ ^ 2 + n₂ ^ 2 + 2 * n₁ * n₂ := sorry

  /-
  ## Fermat's Last Theorem
  -/

  example (a b c n: ℕ): (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := sorry
end Blended
