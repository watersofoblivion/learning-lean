/-
# Multiplication World
-/

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»

/-
## Mul One
-/

theorem ℕ.mulOne: ∀ n: ℕ, n * 1 = n
  | .zero => rfl
  | .succ n =>
    calc n.succ * 1
      _ = n.succ * ℕ.zero.succ       := congrArg (ℕ.mul n.succ) (ℕ.oneSuccOfZero)
      _ = (n.succ * ℕ.zero) + n.succ := ℕ.mulSucc n.succ ℕ.zero
      _ = n.succ + (n.succ * ℕ.zero) := ℕ.addComm (n.succ * ℕ.zero) n.succ
      _ = n.succ + 0                 := congrArg (ℕ.add n.succ) (ℕ.mulZero n.succ)
      _ = n.succ                     := ℕ.add0 n.succ

example (n: ℕ): n * 1 = n := by
  cases n with
    | zero => rfl
    | succ n => simp [ℕ.oneSuccOfZero, ℕ.mulSucc, ℕ.mulZero, ℕ.zeroAdd]

/-
## Zero Mul
-/

theorem ℕ.zeroMul: ∀ n: ℕ, 0 * n = 0
  | .zero => rfl
  | .succ n =>
    calc 0 * n.succ
      _ = 0 * n + 0 := ℕ.mulSucc 0 n
      _ = 0 * n     := ℕ.addZero (0 * n)
      _ = 0         := ℕ.zeroMul n

example (n: ℕ): 0 * n = 0 := by
  induction n with
    | zero => rfl
    | succ n ih =>
      simp [ℕ.mulSucc, ℕ.add0]
      rw [ih]

/-
## Successor Mul
-/

theorem ℕ.succMul: ∀ n₁ n₂: ℕ, n₁.succ * n₂ = n₁ * n₂ + n₂
  | n₁, .zero =>
    calc n₁.succ * ℕ.zero
      _ = 0          := ℕ.mulZero n₁.succ
      _ = n₁ * 0     := Eq.symm (ℕ.mulZero n₁)
      _ = n₁ * 0 + 0 := Eq.symm (ℕ.addZero (n₁ * 0))
  | n₁, .succ n₂ =>
    calc n₁.succ * n₂.succ
      _ = n₁.succ * n₂ + n₁.succ   := ℕ.mulSucc n₁.succ n₂
      _ = n₁.succ + n₁.succ * n₂   := ℕ.addComm (n₁.succ * n₂) n₁.succ
      _ = n₁.succ + (n₁ * n₂ + n₂) := congrArg (ℕ.add n₁.succ) (ℕ.succMul n₁ n₂)
      _ = n₁ * n₂ + n₂ + n₁.succ   := ℕ.addComm n₁.succ (n₁ * n₂ + n₂)
      _ = n₁ * n₂.succ + n₂.succ   := sorry

example (n₁ n₂: ℕ): n₁.succ * n₂ = n₁ * n₂ + n₂ := by
  induction n₂ with
    | zero => simp [ℕ.mulZero, ℕ.addZero]
    | succ n₂ ih => sorry

/-
## Mul Commutative
-/

theorem ℕ.mulComm: ∀ n₁ n₂: ℕ, n₁ * n₂ = n₂ * n₁
  | .zero, n₂ =>
    calc ℕ.zero * n₂
      _ = 0      := ℕ.zeroMul n₂
      _ = n₂ * 0 := Eq.symm (ℕ.mul0 n₂)
  | .succ n₁, n₂ =>
    calc n₁.succ * n₂
      _ = n₁ * n₂ + n₂ := ℕ.succMul n₁ n₂
      _ = n₂ + n₁ * n₂ := ℕ.addComm (n₁ * n₂) n₂
      _ = n₂ + n₂ * n₁ := congrArg (ℕ.add n₂) (ℕ.mulComm n₁ n₂)
      _ = n₂ * n₁ + n₂ := ℕ.addComm n₂ (n₂ * n₁)
      _ = n₂ * n₁.succ := Eq.symm (ℕ.mulSucc n₂ n₁)

example (n₁ n₂: ℕ): n₁ * n₂ = n₂ * n₁ := by
  induction n₁ with
    | zero =>
      have h: ℕ.zero = 0 := rfl
      rw [ℕ.mulZero, h, ℕ.zeroMul]
    | succ n₁ ih =>
      simp [ℕ.succMul]
      rw [ih]
      simp [ℕ.mulSucc]

/-
## One Mul
-/

theorem ℕ.oneMul: ∀ n: ℕ, 1 * n = n
  | .zero => ℕ.mul0 1
  | .succ n =>
    calc 1 * n.succ
      _ = 1 * n + 1 := ℕ.mulSucc 1 n
      _ = 1 + 1 * n := ℕ.addComm (1 * n) 1
      _ = 1 + n     := congrArg (ℕ.add 1) (ℕ.oneMul n)
      _ = n + 1     := ℕ.addComm 1 n
      _ = n.succ    := Eq.symm (ℕ.succEqAddOne n)

example (n: ℕ): 1 * n = n := by
  induction n with
    | zero => rw [ℕ.mulZero]
    | succ n ih =>
      simp [ℕ.mulSucc]
      rw [ih]
      simp [ℕ.succEqAddOne]

/-
## Two Mul
-/

theorem ℕ.twoMul: ∀ n: ℕ, 2 * n = n + n
  | .zero => ℕ.mulZero 2
  | .succ n =>
    calc 2 * n.succ
      _ = 2 * n + 2             := ℕ.mulSucc 2 n
      _ = 2 + 2 * n             := ℕ.addComm (2 * n) 2
      _ = 2 + (n + n)           := congrArg (ℕ.add 2) (ℕ.twoMul n)
      _ = n + n + 2             := ℕ.addComm 2 (n + n)
      _ = n + n + (1: ℕ).succ   := sorry -- congrArg (Nat.add (n + n)) ℕ.twoSuccOfOne
      _ = n + (n + (1: ℕ).succ) := ℕ.addAssoc n n (1: ℕ).succ
      _ = n + (n + (1: ℕ)).succ := congrArg (ℕ.add n) (ℕ.addSucc n (1: ℕ))
      _ = n + n.succ.succ       := congrArg (ℕ.add n) (congrArg ℕ.succ (Eq.symm (ℕ.succEqAddOne n)))
      _ = n.succ + n.succ       := ℕ.addSucc n n.succ

example (n: ℕ): 2 * n = n + n := by
  induction n with
    | zero => rfl
    | succ n ih =>
      simp [ℕ.mulSucc]
      rw [ih]
      simp [ℕ.twoSuccOfOne, ℕ.oneSuccOfZero, ℕ.addSucc, ℕ.succAdd, ℕ.addZero]

/-
## Mul Add
-/

theorem ℕ.mulAdd: ∀ n₁ n₂ n₃: ℕ, n₁ * (n₂ + n₃) = n₁ * n₂ + n₁ * n₃
  | .zero, n₂, n₃ =>
    calc 0 * (n₂ + n₃)
      _ = 0               := ℕ.zeroMul (n₂ + n₃)
      _ = 0 * n₂          := Eq.symm (ℕ.zeroMul n₂)
      _ = 0 * n₂ + 0      := Eq.symm (ℕ.addZero (0 * n₂))
      _ = 0 * n₂ + 0 * n₃ := congrArg (ℕ.add (0 * n₂)) (Eq.symm (ℕ.zeroMul n₃))
  | .succ n₁, n₂, n₃ =>
    calc n₁.succ * (n₂ + n₃)
      _ = n₁ * (n₂ + n₃) + (n₂ + n₃)      := ℕ.succMul n₁ (n₂ + n₃)
      _ = n₂ + n₃ + n₁ * (n₂ + n₃)        := ℕ.addComm (n₁ * (n₂ + n₃)) (n₂ + n₃)
      _ = n₂ + n₃ + n₁ * n₂ + n₁ * n₃     := sorry -- congrArg (ℕ.add (n₂ + n₃)) (ℕ.mulAdd n₁ n₂ n₃)
      _ = n₁ * n₃ + (n₂ + n₃ + n₁ * n₂)   := sorry -- ℕ.addComm (n₁ * n₃) (n₂ + n₃ + n₁ * n₂)
      _ = n₂ + (n₃ + n₁ * n₂ + n₁ * n₃)   := congrArg (ℕ.add (n₁ * n₃) (Eq.symm (ℕ.addAssoc n₂ n₃ (n₁ * n₂))))
      _ = n₂ + (n₃ + n₁ * n₃ + n₁ * n₂)   := congrArg (ℕ.add n₂) (ℕ.addRightComm n₃ (n₁ * n₂) (n₁ * n₃))
      _ = n₂ + (n₁ * n₂ + (n₃ + n₁ * n₃)) := congrArg (ℕ.add n₂) (ℕ.addComm (n₃ + n₁ * n₃) (n₁ * n₂))
      _ = n₂ + n₁ * n₂ + (n₃ + n₁ * n₃)   := Eq.symm (ℕ.addAssoc n₂ (n₁ * n₂) (n₃ + n₁ * n₃))
      _ = n₂ + n₁ * n₂ + (n₁ * n₃ + n₃)   := congrArg (ℕ.add (n₂ + n₁ * n₂)) (ℕ.addComm n₃ (n₁ * n₃))
      _ = n₂ + n₁ * n₂ + (n₁.succ * n₃)   := congrArg (ℕ.add (n₂ + n₁ * n₂)) (Eq.symm (ℕ.succMul n₁ n₃))
      _ = n₁.succ * n₃ + (n₂ + n₁ * n₂)   := ℕ.addComm (n₂ + n₁ * n₂) (n₁.succ * n₃)
      _ = n₁.succ * n₃ + (n₁ * n₂ + n₂)   := congrArg (ℕ.add (n₁.succ * n₃)) (ℕ.addComm n₂ (n₁ * n₂))
      _ = n₁.succ * n₃ + n₁.succ * n₂     := congrArg (ℕ.add (n₁.succ * n₃)) (Eq.symm (ℕ.succMul n₁ n₂))
      _ = n₁.succ * n₂ + n₁.succ * n₃     := ℕ.addComm (n₁.succ * n₃) (n₁.succ * n₂)

example (n₁ n₂ n₃: ℕ): n₁ * (n₂ + n₃) = n₁ * n₂ + n₁ * n₃ := by
  induction n₁ with
    | zero =>
      repeat rw [ℕ.mulComm, ℕ.mulZero]
      rw [ℕ.addZero]
    | succ n ih => sorry

/-
## Add Mul
-/

theorem ℕ.addMul: ∀ n₁ n₂ n₃: ℕ, (n₁ + n₂) * n₃ = n₁ * n₃ + n₃ * n₄ := sorry

example (n₁ n₂ n₃: ℕ): (n₁ + n₂) * n₃ = n₁ * n₃ + n₃ * n₄ := by
  sorry

/-
## Mul Assoc
-/

theorem ℕ.mulAssoc: ∀ n₁ n₂ n₃: ℕ, (n₁ * n₂) * n₃ = n₁ * (n₂ * n₃) := sorry

example (n₁ n₂ n₃: ℕ): (n₁ * n₂) * n₃ = n₁ * (n₂ * n₃) := by
  sorry
