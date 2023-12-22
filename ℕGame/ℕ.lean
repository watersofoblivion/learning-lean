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
  | .zero, _ | _, .zero => .zero
  | .succ n₁, n₂ => (n₁.mul n₂).add n₂

section Instances
  /-- Coerce instances of our custom `ℕ` into instances of `Nat` from the Lean prelude. -/
  instance: Coe ℕ Nat where coe := ℕ.toNat

  /-- Coerce instances `Nat` from the Lean prelude into our custom `ℕ`.  This is the base case.  -/
  instance: OfNat ℕ 0 where ofNat := ℕ.zero

  /-- Coerce instances `Nat` from the Lean prelude into our custom `ℕ`.  This is the inductive case. -/
  instance: OfNat ℕ (n + 1) where ofNat := (ℕ.ofNat n).succ

  /-- Add two instances of `ℕ`. -/
  instance: Add ℕ where add := ℕ.add

  /-- Multiply two instances of `ℕ`. -/
  instance: Mul ℕ where mul := ℕ.mul
end Instances

/-- Less than or equals -/
def ℕ.lte (n₁ n₂: ℕ): Prop :=
  ∃ (n₃: ℕ), n₂ = n₁ + n₃

/-- Less than -/
def ℕ.lt (n₁ n₂: ℕ): Prop :=
  n₁.lte n₂ ∧ ¬(¬n₂.lte n₁)

section Instances
  instance: LE ℕ where le := ℕ.lte
  instance: LT ℕ where lt := ℕ.lt
end Instances

/-
## Supplied Theorems
-/

section Successors
  /-- One is the successor of zero.  This explicitly uses `0` instead of `ℕ.zero`. -/
  theorem ℕ.oneSuccOf0: 1 = ℕ.succ 0 := by rfl

  /-- One is the successor of zero.  This explicitly uses `ℕ.zero` instead of `0`. -/
  theorem ℕ.oneSuccOfZero: 1 = ℕ.succ ℕ.zero := by rfl

  /-- Two is the successor of one. -/
  theorem ℕ.twoSuccOfOne: 2 = ℕ.succ 1 := by rfl

  /-- Three is the successor of two. -/
  theorem ℕ.threeSuccOfTwo: 3 = ℕ.succ 2 := by rfl

  /-- Four is the successor of three. -/
  theorem ℕ.fourSuccOfThree: 4 = ℕ.succ 3 := by rfl

  /-- Five is the successor of four. -/
  theorem ℕ.fiveSuccOfFour: 5 = ℕ.succ 4 := by rfl
end Successors

section Identity
  /-- Zero is the right identity.  Explicitly uses `0`, not `ℕ.zero`. -/
  theorem ℕ.add0 (n: ℕ): n + 0 = n := by
    cases n <;> rfl

  /-- Zero is the right identity.  Explicitly uses `ℕ.zero`, not `0`. -/
  theorem ℕ.addZero (n: ℕ): n + .zero = n := by
    cases n <;> rfl
end Identity

section Successor
  theorem ℕ.addSucc (n₁ n₂: ℕ): n₁ + succ n₂ = succ (n₁ + n₂) := by
    induction n₁ with
      | zero => sorry
        -- rw [ℕ.zeroAdd, ℕ.zeroAdd]
      | succ n₁ ihₙ₁ => sorry
section Successor

section Peano
  axiom ℕ.succInj (n₁ n₂: ℕ): n₁.succ = n₂.succ → n₁ = n₂
  axiom ℕ.zeroNeSucc (n: ℕ): 0 ≠ n.succ
end Peano

section Inequality
  @[symm] def neSymm {α: Type} (x y: α): x ≠ y → y ≠ x := Ne.symm
end Inequality
