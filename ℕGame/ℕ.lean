/-
# ℕ
-/

import Mathlib.Init.Core
import Mathlib.Tactic.Relation.Symm

/-- Our own implementation of the natural numbers, `ℕ`, to use for the (Natural Number Game)[https://adam.math.hhu.de/#/g/hhu-adam/NNG4].  -/
inductive ℕ: Type where
  | zero: ℕ
  | succ: ℕ → ℕ

/-- Convert a `Nat` from the Lean prelude into our custom `ℕ` type -/
def ℕ.ofNat: Nat → ℕ
  | .zero => .zero
  | .succ n => .succ (ofNat n)

/-- Convert our custom `ℕ` type into a `Nat` from the Lean prelude -/
def ℕ.toNat: ℕ → Nat
  | .zero => .zero
  | .succ n => 1 + n.toNat

/-- Add two natural numbers -/
def ℕ.add: ℕ → ℕ → ℕ
  | .zero, n | n, .zero  => n
  | .succ n₁, n₂ => (n₁.add n₂).succ

/-- Multiply two natural numbers -/
def ℕ.mul: ℕ → ℕ → ℕ
  | _, .zero => .zero
  | n₁, .succ n₂ => (n₁.mul n₂).add n₂

def ℕ.pow: ℕ → ℕ → ℕ
  | _, .zero => .zero
  | n₁, .succ n₂ => (n₁.pow n₂).mul n₁

/-- Less than or equals -/
def ℕ.lte (n₁ n₂: ℕ): Prop :=
  ∃ (n₃: ℕ), n₂ = n₁.add n₃

/-- Less than -/
def ℕ.lt (n₁ n₂: ℕ): Prop :=
  n₁.lte n₂ ∧ ¬(¬n₂.lte n₁)

section Instances
  /-- Coerce instances `Nat` from the Lean prelude into our custom `ℕ`.  This is the base case.  -/
  instance: OfNat ℕ 0 where ofNat := ℕ.zero

  /-- Coerce instances `Nat` from the Lean prelude into our custom `ℕ`.  This is the inductive case. -/
  instance: OfNat ℕ (n + 1) where ofNat := (ℕ.ofNat n).succ

  /-- Add two instances of `ℕ`. -/
  instance: Add ℕ where add := ℕ.add

  /-- Multiply two instances of `ℕ`. -/
  instance: Mul ℕ where mul := ℕ.mul

  /-- Exponentiation of `ℕ` to `ℕ` -/
  instance: Pow ℕ ℕ where pow := ℕ.pow

  /-- Comparison of ℕ ≤ ℕ -/
  instance: LE ℕ where le := ℕ.lte

  /-- Comparison of ℕ < ℕ -/
  instance: LT ℕ where lt := ℕ.lt
end Instances

section Zero
  /-- Conversion between `ℕ.zero` and the numeral `0` -/
  theorem ℕ.zeroNumeral: ℕ.zero = (0: ℕ) := rfl

  /-- Conversion between the numeral `0` and `ℕ.zero` -/
  theorem ℕ.numeralZero: (0: ℕ) = ℕ.zero := rfl
end Zero

/-
## Supplied Theorems
-/

section Successors
  /-- One is the successor of zero.  This explicitly uses `0` instead of `ℕ.zero`. -/
  theorem ℕ.oneSuccOf0: (1: ℕ) = (0: ℕ).succ := rfl

  /-- One is the successor of zero.  This explicitly uses `ℕ.zero` instead of `0`. -/
  theorem ℕ.oneSuccOfZero: (1: ℕ) = ℕ.zero.succ := rfl

  /-- Two is the successor of one. -/
  theorem ℕ.twoSuccOfOne: (2: ℕ) = (1: ℕ).succ := rfl

  /-- Three is the successor of two. -/
  theorem ℕ.threeSuccOfTwo: (3: ℕ) = (2: ℕ).succ := rfl

  /-- Four is the successor of three. -/
  theorem ℕ.fourSuccOfThree: (4: ℕ) = (3: ℕ).succ := rfl

  /-- Five is the successor of four. -/
  theorem ℕ.fiveSuccOfFour: (5: ℕ) = (4: ℕ).succ := rfl
end Successors

section Identity
  /-- Zero is the right identity.  Explicitly uses `0`, not `ℕ.zero`. -/
  @[simp]
  theorem ℕ.add0: ∀ n: ℕ, n + (0: ℕ) = n
    | .zero => rfl
    | .succ _ => rfl

  /-- Zero is the right identity.  Explicitly uses `ℕ.zero`, not `0`. -/
  @[simp]
  theorem ℕ.addZero: ∀ n: ℕ, n + ℕ.zero = n
    | .zero => rfl
    | .succ _ => rfl
end Identity

section Successor
  /-- Addition of successor is equivalent to the successor of addition -/
  @[simp]
  theorem ℕ.addSucc (n₁ n₂: ℕ): n₁ + n₂.succ = (n₁ + n₂).succ := by
    induction n₂ with
      | zero =>
        rw [ℕ.addZero, ← ℕ.oneSuccOfZero]
        sorry
      | succ n₂ ihₙ₁ =>
        rw [ihₙ₁]
        sorry
section Successor

section Peano
  @[simp]
  axiom ℕ.succInj (n₁ n₂: ℕ): n₁.succ = n₂.succ → n₁ = n₂

  @[simp]
  axiom ℕ.zeroNeSucc (n: ℕ): (0: ℕ) ≠ n.succ
end Peano

section Inequality
  @[symm] def neSymm {α: Type} (x y: α): x ≠ y → y ≠ x := Ne.symm
end Inequality

section Multiplication
  @[simp]
  theorem ℕ.mul0: ∀ n: ℕ, n * (0: ℕ) = (0: ℕ) := sorry

  @[simp]
  theorem ℕ.mulZero: ∀ n: ℕ, n * ℕ.zero = ℕ.zero := sorry

  @[simp]
  theorem ℕ.mulSucc: ∀ n₁ n₂: ℕ, n₁ * n₂.succ = n₁ * n₂ + n₁ := sorry
end Multiplication

section Exponentiation
  @[simp]
  theorem ℕ.pow0: ∀ n: ℕ, n ^ (0: ℕ) = (1: ℕ) := sorry

  @[simp]
  theorem ℕ.powZero: ∀ n: ℕ, n ^ ℕ.zero = (1: ℕ) := sorry

  @[simp]
  theorem ℕ.powSucc: ∀ n₁ n₂: ℕ, n₁ ^ n₂.succ = n₁ ^ n₂ * n₁ := sorry
end Exponentiation
