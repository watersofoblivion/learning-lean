/-
# ℕ
-/

import Mathlib.Init.Core
import Mathlib.Tactic.Relation.Symm

/-- Our own implementation of the natural numbers, `ℕ`, to use for the (Natural Number Game)[https://adam.math.hhu.de/#/g/hhu-adam/NNG4].  -/
inductive ℕ: Type where
  | zero: ℕ
  | succ: ℕ → ℕ

def ℕ.ofNat: Nat → ℕ
  | .zero => .zero
  | .succ n => .succ (ofNat n)

def ℕ.add: ℕ → ℕ → ℕ
  | .zero, n | n, .zero  => n
  | .succ n₁, n₂ => (n₁.add n₂).succ

def ℕ.mul: ℕ → ℕ → ℕ
  | _, .zero => .zero
  | n₁, .succ n₂ => (n₁.mul n₂).add n₂

def ℕ.pow: ℕ → ℕ → ℕ
  | _, .zero => .zero
  | n₁, .succ n₂ => (n₁.pow n₂).mul n₁

def ℕ.lte (n₁ n₂: ℕ): Prop :=
  ∃ (n₃: ℕ), n₂ = n₁.add n₃

def ℕ.lt (n₁ n₂: ℕ): Prop :=
  n₁.lte n₂ ∧ ¬(¬n₂.lte n₁)

section Instances
  instance: OfNat ℕ 0 where ofNat := ℕ.zero
  instance: OfNat ℕ (n + 1) where ofNat := (ℕ.ofNat n).succ

  instance: Add ℕ where add := ℕ.add
  instance: Mul ℕ where mul := ℕ.mul
  instance: Pow ℕ ℕ where pow := ℕ.pow

  instance: LE ℕ where le := ℕ.lte
  instance: LT ℕ where lt := ℕ.lt
end Instances

namespace Term
  /-
  ## Supplied Theorems
  -/

  /-
  ### Zero
  -/

  axiom zeroNumeral: ℕ.zero = (0: ℕ)
  axiom numeralZero: (0: ℕ) = ℕ.zero

  /-
  ### Successors
  -/

  axiom oneSuccOf0: (1: ℕ) = (0: ℕ).succ
  axiom oneSuccOfZero: (1: ℕ) = ℕ.zero.succ
  axiom twoSuccOfOne: (2: ℕ) = (1: ℕ).succ
  axiom threeSuccOfTwo: (3: ℕ) = (2: ℕ).succ
  axiom fourSuccOfThree: (4: ℕ) = (3: ℕ).succ
  axiom fiveSuccOfFour: (5: ℕ) = (4: ℕ).succ

  /-
  ### Identity
  -/

  axiom add0: ∀ n: ℕ, n + (0: ℕ) = n
  axiom addZero: ∀ n: ℕ, n + ℕ.zero = n

  /-
  ### Successor
  -/

  axiom addSucc (n₁ n₂: ℕ): n₁ + n₂.succ = (n₁ + n₂).succ

  /-
  ### Peano
  -/

  axiom succInj (n₁ n₂: ℕ): n₁.succ = n₂.succ → n₁ = n₂
  axiom zeroNeSucc (n: ℕ): (0: ℕ) ≠ n.succ

  /-
  ### Inequality
  -/

  @[symm] def neSymm {α: Type} (x y: α): x ≠ y → y ≠ x := Ne.symm

  /-
  ### Multiplication
  -/

  axiom mul0: ∀ n: ℕ, n * (0: ℕ) = (0: ℕ)
  axiom mulZero: ∀ n: ℕ, n * ℕ.zero = ℕ.zero
  axiom mulSucc: ∀ n₁ n₂: ℕ, n₁ * n₂.succ = n₁ * n₂ + n₁

  /-
  ### Exponentiation
  -/

  axiom pow0: ∀ n: ℕ, n ^ (0: ℕ) = (1: ℕ)
  axiom powZero: ∀ n: ℕ, n ^ ℕ.zero = (1: ℕ)
  axiom powSucc: ∀ n₁ n₂: ℕ, n₁ ^ n₂.succ = n₁ ^ n₂ * n₁
end Term

namespace Tactic
  /-
  ## Supplied Theorems
  -/

  /-
  ### Zero
  -/

  axiom zeroNumeral: ℕ.zero = (0: ℕ)
  axiom numeralZero: (0: ℕ) = ℕ.zero

  /-
  ### Successors
  -/

  axiom oneSuccOf0: (1: ℕ) = (0: ℕ).succ
  axiom oneSuccOfZero: (1: ℕ) = ℕ.zero.succ
  axiom twoSuccOfOne: (2: ℕ) = (1: ℕ).succ
  axiom threeSuccOfTwo: (3: ℕ) = (2: ℕ).succ
  axiom fourSuccOfThree: (4: ℕ) = (3: ℕ).succ
  axiom fiveSuccOfFour: (5: ℕ) = (4: ℕ).succ

  /-
  ### Identity
  -/

  @[scoped simp] axiom add0: ∀ n: ℕ, n + (0: ℕ) = n
  @[scoped simp] axiom addZero: ∀ n: ℕ, n + ℕ.zero = n

  /-
  ### Successor
  -/

  @[scoped simp] axiom addSucc (n₁ n₂: ℕ): n₁ + n₂.succ = (n₁ + n₂).succ

  /-
  ### Peano
  -/

  @[scoped simp] axiom succInj (n₁ n₂: ℕ): n₁.succ = n₂.succ → n₁ = n₂
  @[scoped simp] axiom zeroNeSucc (n: ℕ): (0: ℕ) ≠ n.succ

  /-
  ### Inequality
  -/

  @[symm] def neSymm {α: Type} (x y: α): x ≠ y → y ≠ x := Ne.symm

  /-
  ### Multiplication
  -/

  @[scoped simp] axiom mul0: ∀ n: ℕ, n * (0: ℕ) = (0: ℕ)
  @[scoped simp] axiom mulZero: ∀ n: ℕ, n * ℕ.zero = ℕ.zero
  @[scoped simp] axiom mulSucc: ∀ n₁ n₂: ℕ, n₁ * n₂.succ = n₁ * n₂ + n₁

  /-
  ### Exponentiation
  -/

  @[scoped simp] axiom pow0: ∀ n: ℕ, n ^ (0: ℕ) = (1: ℕ)
  @[scoped simp] axiom powZero: ∀ n: ℕ, n ^ ℕ.zero = (1: ℕ)
  @[scoped simp] axiom powSucc: ∀ n₁ n₂: ℕ, n₁ ^ n₂.succ = n₁ ^ n₂ * n₁
end Tactic

namespace Blended
  /-
  ## Supplied Theorems
  -/

  /-
  ### Zero
  -/

  axiom zeroNumeral: ℕ.zero = (0: ℕ)
  axiom numeralZero: (0: ℕ) = ℕ.zero

  /-
  ### Successors
  -/

  axiom oneSuccOf0: (1: ℕ) = (0: ℕ).succ
  axiom oneSuccOfZero: (1: ℕ) = ℕ.zero.succ
  axiom twoSuccOfOne: (2: ℕ) = (1: ℕ).succ
  axiom threeSuccOfTwo: (3: ℕ) = (2: ℕ).succ
  axiom fourSuccOfThree: (4: ℕ) = (3: ℕ).succ
  axiom fiveSuccOfFour: (5: ℕ) = (4: ℕ).succ

  /-
  ### Identity
  -/

  @[scoped simp] axiom add0: ∀ n: ℕ, n + (0: ℕ) = n
  @[scoped simp] axiom addZero: ∀ n: ℕ, n + ℕ.zero = n

  /-
  ### Successor
  -/

  @[scoped simp] axiom addSucc (n₁ n₂: ℕ): n₁ + n₂.succ = (n₁ + n₂).succ

  /-
  ### Peano
  -/

  @[scoped simp] axiom succInj (n₁ n₂: ℕ): n₁.succ = n₂.succ → n₁ = n₂
  @[scoped simp] axiom zeroNeSucc (n: ℕ): (0: ℕ) ≠ n.succ

  /-
  ### Inequality
  -/

  @[symm] def neSymm {α: Type} (x y: α): x ≠ y → y ≠ x := Ne.symm

  /-
  ### Multiplication
  -/

  @[scoped simp] axiom mul0: ∀ n: ℕ, n * (0: ℕ) = (0: ℕ)
  @[scoped simp] axiom mulZero: ∀ n: ℕ, n * ℕ.zero = ℕ.zero
  @[scoped simp] axiom mulSucc: ∀ n₁ n₂: ℕ, n₁ * n₂.succ = n₁ * n₂ + n₁

  /-
  ### Exponentiation
  -/

  @[scoped simp] axiom pow0: ∀ n: ℕ, n ^ (0: ℕ) = (1: ℕ)
  @[scoped simp] axiom powZero: ∀ n: ℕ, n ^ ℕ.zero = (1: ℕ)
  @[scoped simp] axiom powSucc: ∀ n₁ n₂: ℕ, n₁ ^ n₂.succ = n₁ ^ n₂ * n₁
end Blended
