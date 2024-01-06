/-
# Multiplication World
-/

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»

namespace Term
  /-
  ## Mul One
  -/

  theorem mulOne: ∀ n: ℕ, n * (1: ℕ) = n
    | .zero => rfl
    | .succ n =>
      calc n.succ * 1
        _ = n.succ * ℕ.zero.succ       := congrArg (ℕ.mul n.succ) (oneSuccOfZero)
        _ = (n.succ * ℕ.zero) + n.succ := mulSucc n.succ ℕ.zero
        _ = n.succ + (n.succ * ℕ.zero) := addComm (n.succ * ℕ.zero) n.succ
        _ = n.succ + 0                 := congrArg (ℕ.add n.succ) (mulZero n.succ)
        _ = n.succ                     := add0 n.succ

  /-
  ## Zero Mul
  -/

  theorem zeroMul: ∀ n: ℕ, (0: ℕ) * n = (0: ℕ)
    | .zero => rfl
    | .succ n =>
      calc 0 * n.succ
        _ = 0 * n + 0 := mulSucc 0 n
        _ = 0 * n     := addZero (0 * n)
        _ = 0         := zeroMul n

  /-
  ## Successor Mul
  -/

  theorem succMul: ∀ n₁ n₂: ℕ, n₁.succ * n₂ = n₁ * n₂ + n₂
    | n₁, .zero =>
      calc n₁.succ * ℕ.zero
        _ = 0          := mulZero n₁.succ
        _ = n₁ * 0     := Eq.symm (mulZero n₁)
        _ = n₁ * 0 + 0 := Eq.symm (addZero (n₁ * 0))
    | n₁, .succ n₂ =>
      calc n₁.succ * n₂.succ
        _ = n₁.succ * n₂ + n₁.succ   := mulSucc n₁.succ n₂
        _ = n₁.succ + n₁.succ * n₂   := addComm (n₁.succ * n₂) n₁.succ
        _ = n₁.succ + (n₁ * n₂ + n₂) := congrArg (ℕ.add n₁.succ) (succMul n₁ n₂)
        _ = n₁ * n₂ + n₂ + n₁.succ   := addComm n₁.succ (n₁ * n₂ + n₂)
        _ = n₁ * n₂.succ + n₂.succ   := sorry

  /-
  ## Mul Commutative
  -/

  theorem mulComm: ∀ n₁ n₂: ℕ, n₁ * n₂ = n₂ * n₁
    | .zero, n₂ =>
      calc ℕ.zero * n₂
        _ = 0      := zeroMul n₂
        _ = n₂ * 0 := Eq.symm (mul0 n₂)
    | .succ n₁, n₂ =>
      calc n₁.succ * n₂
        _ = n₁ * n₂ + n₂ := succMul n₁ n₂
        _ = n₂ + n₁ * n₂ := addComm (n₁ * n₂) n₂
        _ = n₂ + n₂ * n₁ := congrArg (ℕ.add n₂) (mulComm n₁ n₂)
        _ = n₂ * n₁ + n₂ := addComm n₂ (n₂ * n₁)
        _ = n₂ * n₁.succ := Eq.symm (mulSucc n₂ n₁)

  /-
  ## One Mul
  -/

  theorem oneMul: ∀ n: ℕ, (1: ℕ) * n = n
    | .zero => mul0 1
    | .succ n =>
      calc 1 * n.succ
        _ = 1 * n + 1 := mulSucc 1 n
        _ = 1 + 1 * n := addComm (1 * n) 1
        _ = 1 + n     := congrArg (ℕ.add 1) (oneMul n)
        _ = n + 1     := addComm 1 n
        _ = n.succ    := Eq.symm (succEqAddOne n)

  /-
  ## Two Mul
  -/

  theorem twoMul: ∀ n: ℕ, (2: ℕ) * n = n + n
    | .zero => mulZero 2
    | .succ n =>
      calc 2 * n.succ
        _ = 2 * n + 2             := mulSucc 2 n
        _ = 2 + 2 * n             := addComm (2 * n) 2
        _ = 2 + (n + n)           := congrArg (ℕ.add 2) (twoMul n)
        _ = n + n + 2             := addComm 2 (n + n)
        _ = n + n + (1: ℕ).succ   := sorry -- congrArg (Nat.add (n + n)) twoSuccOfOne
        _ = n + (n + (1: ℕ).succ) := addAssoc n n (1: ℕ).succ
        _ = n + (n + (1: ℕ)).succ := congrArg (ℕ.add n) (addSucc n (1: ℕ))
        _ = n + n.succ.succ       := congrArg (ℕ.add n) (congrArg ℕ.succ (Eq.symm (succEqAddOne n)))
        _ = n.succ + n.succ       := addSucc n n.succ

  /-
  ## Mul Add
  -/

  theorem mulAdd: ∀ n₁ n₂ n₃: ℕ, n₁ * (n₂ + n₃) = n₁ * n₂ + n₁ * n₃
    | .zero, n₂, n₃ =>
      calc 0 * (n₂ + n₃)
        _ = 0               := zeroMul (n₂ + n₃)
        _ = 0 * n₂          := Eq.symm (zeroMul n₂)
        _ = 0 * n₂ + 0      := Eq.symm (addZero (0 * n₂))
        _ = 0 * n₂ + 0 * n₃ := congrArg (ℕ.add (0 * n₂)) (Eq.symm (zeroMul n₃))
    | .succ n₁, n₂, n₃ =>
      calc n₁.succ * (n₂ + n₃)
        _ = n₁ * (n₂ + n₃) + (n₂ + n₃)      := succMul n₁ (n₂ + n₃)
        _ = n₂ + n₃ + n₁ * (n₂ + n₃)        := addComm (n₁ * (n₂ + n₃)) (n₂ + n₃)
        _ = n₂ + n₃ + (n₁ * n₂ + n₁ * n₃)   := congrArg (ℕ.add (n₂ + n₃)) (mulAdd n₁ n₂ n₃)
        _ = n₂ + (n₃ + (n₁ * n₂ + n₁ * n₃)) := addAssoc n₂ n₃ (n₁ * n₂ + n₁ * n₃)
        _ = n₂ + (n₃ + n₁ * n₂ + n₁ * n₃)   := congrArg (ℕ.add n₂) (Eq.symm (addAssoc n₃ (n₁ * n₂) (n₁ * n₃)))
        _ = n₂ + (n₃ + n₁ * n₃ + n₁ * n₂)   := congrArg (ℕ.add n₂) (addRightComm n₃ (n₁ * n₂) (n₁ * n₃))
        _ = n₂ + (n₁ * n₂ + (n₃ + n₁ * n₃)) := congrArg (ℕ.add n₂) (addComm (n₃ + n₁ * n₃) (n₁ * n₂))
        _ = n₂ + n₁ * n₂ + (n₃ + n₁ * n₃)   := Eq.symm (addAssoc n₂ (n₁ * n₂) (n₃ + n₁ * n₃))
        _ = n₂ + n₁ * n₂ + (n₁ * n₃ + n₃)   := congrArg (ℕ.add (n₂ + n₁ * n₂)) (addComm n₃ (n₁ * n₃))
        _ = n₂ + n₁ * n₂ + (n₁.succ * n₃)   := congrArg (ℕ.add (n₂ + n₁ * n₂)) (Eq.symm (succMul n₁ n₃))
        _ = n₁.succ * n₃ + (n₂ + n₁ * n₂)   := addComm (n₂ + n₁ * n₂) (n₁.succ * n₃)
        _ = n₁.succ * n₃ + (n₁ * n₂ + n₂)   := congrArg (ℕ.add (n₁.succ * n₃)) (addComm n₂ (n₁ * n₂))
        _ = n₁.succ * n₃ + n₁.succ * n₂     := congrArg (ℕ.add (n₁.succ * n₃)) (Eq.symm (succMul n₁ n₂))
        _ = n₁.succ * n₂ + n₁.succ * n₃     := addComm (n₁.succ * n₃) (n₁.succ * n₂)

  /-
  ## Add Mul
  -/

  theorem addMul: ∀ n₁ n₂ n₃: ℕ, (n₁ + n₂) * n₃ = n₁ * n₃ + n₃ * n₄ := sorry

  /-
  ## Mul Assoc
  -/

  theorem mulAssoc: ∀ n₁ n₂ n₃: ℕ, (n₁ * n₂) * n₃ = n₁ * (n₂ * n₃) := sorry
end Term

namespace Tactic

  /-
  ## Mul One
  -/

  @[scoped simp]
  theorem mulOne (n: ℕ): n * (1: ℕ) = n := by
    cases n with
      | zero => rfl
      | succ n => simp [oneSuccOfZero]

  /-
  ## Zero Mul
  -/

  @[scoped simp]
  theorem zeroMul (n: ℕ): (0: ℕ) * n = (0: ℕ) := by
    induction n with
      | zero => rfl
      | succ n ih =>
        simp
        rw [ih]

  /-
  ## Successor Mul
  -/

  @[scoped simp]
  theorem succMul (n₁ n₂: ℕ): n₁.succ * n₂ = n₁ * n₂ + n₂ := by
    induction n₂ with
      | zero => simp
      | succ n₂ ih => sorry

  /-
  ## Mul Commutative
  -/

  theorem mulComm (n₁ n₂: ℕ): n₁ * n₂ = n₂ * n₁ := by
    induction n₁ with
      | zero =>
        have h: ℕ.zero = 0 := rfl
        simp [h]
      | succ n₁ ih =>
        simp
        rw [ih]

  /-
  ## One Mul
  -/

  @[scoped simp]
  theorem oneMul (n: ℕ): (1: ℕ) * n = n := by
    induction n with
      | zero => simp
      | succ n ih =>
        rw [mulSucc]
        rw [ih]
        simp [succEqAddOne]

  /-
  ## Two Mul
  -/

  @[scoped simp]
  theorem twoMul (n: ℕ): (2: ℕ) * n = n + n := by
    induction n with
      | zero => rfl
      | succ n ih =>
        rw [mulSucc]
        rw [ih]
        simp [twoSuccOfOne, oneSuccOfZero]

  /-
  ## Mul Add
  -/

  @[scoped simp]
  example (n₁ n₂ n₃: ℕ): n₁ * (n₂ + n₃) = n₁ * n₂ + n₁ * n₃ := by
    induction n₁ with
      | zero =>
        have: ℕ.zero = 0 := rfl
        simp_all
      | succ n₁ ih =>
        simp
        rw [ih]
        simp [addComm]
        -- rw [← succMul n₁ n₂, ← succMul n₁ n₃]
        -- rw [← ℕ.addAssoc, ← ℕ.addRightComm, ℕ.addAssoc (n₁ * n₂), ← ℕ.succMul, ℕ.addRightComm, ← ℕ.succMul]
        sorry

  /-
  ## Add Mul
  -/

  @[scoped simp]
  theorem addMul (n₁ n₂ n₃: ℕ): (n₁ + n₂) * n₃ = n₁ * n₃ + n₃ * n₄ := by
    sorry

  /-
  ## Mul Assoc
  -/

  theorem mulAssoc (n₁ n₂ n₃: ℕ): (n₁ * n₂) * n₃ = n₁ * (n₂ * n₃) := by
    sorry
end Tactic

namespace Blended
  /-
  ## Mul One
  -/

  @[scoped simp]
  theorem mulOne: ∀ n: ℕ, n * (1: ℕ) = n
    | .zero => rfl
    | .succ n => by simp [oneSuccOfZero]

  /-
  ## Zero Mul
  -/

  @[scoped simp]
  theorem zeroMul: ∀ n: ℕ, (0: ℕ) * n = (0: ℕ)
    | .zero => rfl
    | .succ n =>
      calc 0 * n.succ
        _ = 0 * n     := by simp
        _ = 0         := by rw [zeroMul n]

  /-
  ## Successor Mul
  -/

  @[scoped simp]
  theorem succMul: ∀ n₁ n₂: ℕ, n₁.succ * n₂ = n₁ * n₂ + n₂
    | n₁, .zero => by simp
    | n₁, .succ n₂ =>
      calc n₁.succ * n₂.succ
        _ = n₁.succ + n₁.succ * n₂   := by simp [addComm]
        _ = n₁.succ + (n₁ * n₂ + n₂) := by rw [succMul n₁ n₂]
        _ = n₁ * n₂ + n₂ + n₁.succ   := by simp [addComm]
        _ = n₁ * n₂.succ + n₂.succ   := sorry

  /-
  ## Mul Commutative
  -/

  theorem mulComm: ∀ n₁ n₂: ℕ, n₁ * n₂ = n₂ * n₁
    | .zero, n₂ =>
      have: ℕ.zero = 0 := by rfl
      by simp_all
    | .succ n₁, n₂ =>
      calc n₁.succ * n₂
        _ = n₂ + n₁ * n₂ := by simp [addComm]
        _ = n₂ + n₂ * n₁ := by rw [mulComm n₁ n₂]
        _ = n₂ * n₁.succ := by simp [addComm]

  /-
  ## One Mul
  -/

  @[scoped simp]
  theorem oneMul: ∀ n: ℕ, (1: ℕ) * n = n
    | .zero => mul0 1
    | .succ n =>
      calc 1 * n.succ
        _ = 1 + 1 * n := by simp [addComm]
        _ = 1 + n     := by rw [oneMul n]
        _ = n.succ    := by sorry -- simp [succEqAddOne, addComm]

  /-
  ## Two Mul
  -/

  @[scoped simp]
  theorem twoMul: ∀ n: ℕ, (2: ℕ) * n = n + n
    | .zero => mulZero 2
    | .succ n =>
      calc 2 * n.succ
        _ = 2 + 2 * n             := by simp [addComm]
        _ = 2 + (n + n)           := by rw [twoMul n]
        -- _ = n + n + 2             := ℕ.addComm 2 (n + n)
        -- _ = n + n + (1: ℕ).succ   := sorry -- congrArg (Nat.add (n + n)) ℕ.twoSuccOfOne
        -- _ = n + (n + (1: ℕ).succ) := ℕ.addAssoc n n (1: ℕ).succ
        -- _ = n + (n + (1: ℕ)).succ := congrArg (ℕ.add n) (addSucc n (1: ℕ))
        -- _ = n + n.succ.succ       := congrArg (ℕ.add n) (congrArg ℕ.succ (Eq.symm (ℕ.succEqAddOne n)))

        -- _ = n.succ + n.succ       := by simp [addComm, addAssoc, ℕ.twoSuccOfOne, succEqAddOne] --addSucc n n.succ

        _ = n.succ + n.succ       := sorry

  /-
  ## Mul Add
  -/

  @[scoped simp]
  theorem mulAdd: ∀ n₁ n₂ n₃: ℕ, n₁ * (n₂ + n₃) = n₁ * n₂ + n₁ * n₃
    | .zero, n₂, n₃ =>
      have: ℕ.zero = 0 := rfl
      by simp_all
    | .succ n₁, n₂, n₃ =>
      calc n₁.succ * (n₂ + n₃)
        _ = n₂ + n₃ + n₁ * (n₂ + n₃)        := by simp [addComm]
        _ = n₂ + n₃ + (n₁ * n₂ + n₁ * n₃)   := by rw [mulAdd n₁ n₂ n₃]
        -- _ = n₂ + (n₃ + (n₁ * n₂ + n₁ * n₃)) := ℕ.addAssoc n₂ n₃ (n₁ * n₂ + n₁ * n₃)
        -- _ = n₂ + (n₃ + n₁ * n₂ + n₁ * n₃)   := congrArg (ℕ.add n₂) (Eq.symm (ℕ.addAssoc n₃ (n₁ * n₂) (n₁ * n₃)))
        -- _ = n₂ + (n₃ + n₁ * n₃ + n₁ * n₂)   := congrArg (ℕ.add n₂) (ℕ.addRightComm n₃ (n₁ * n₂) (n₁ * n₃))
        -- _ = n₂ + (n₁ * n₂ + (n₃ + n₁ * n₃)) := congrArg (ℕ.add n₂) (ℕ.addComm (n₃ + n₁ * n₃) (n₁ * n₂))
        -- _ = n₂ + n₁ * n₂ + (n₃ + n₁ * n₃)   := Eq.symm (ℕ.addAssoc n₂ (n₁ * n₂) (n₃ + n₁ * n₃))
        -- _ = n₂ + n₁ * n₂ + (n₁ * n₃ + n₃)   := congrArg (ℕ.add (n₂ + n₁ * n₂)) (ℕ.addComm n₃ (n₁ * n₃))
        -- _ = n₂ + n₁ * n₂ + (n₁.succ * n₃)   := congrArg (ℕ.add (n₂ + n₁ * n₂)) (Eq.symm (ℕ.succMul n₁ n₃))
        -- _ = n₁.succ * n₃ + (n₂ + n₁ * n₂)   := ℕ.addComm (n₂ + n₁ * n₂) (n₁.succ * n₃)
        -- _ = n₁.succ * n₃ + (n₁ * n₂ + n₂)   := congrArg (ℕ.add (n₁.succ * n₃)) (ℕ.addComm n₂ (n₁ * n₂))
        -- _ = n₁.succ * n₃ + n₁.succ * n₂     := congrArg (ℕ.add (n₁.succ * n₃)) (Eq.symm (ℕ.succMul n₁ n₂))
        -- _ = n₁.succ * n₂ + n₁.succ * n₃     := ℕ.addComm (n₁.succ * n₃) (n₁.succ * n₂)

        _ = n₁.succ * n₂ + n₁.succ * n₃     := sorry

  /-
  ## Add Mul
  -/

  @[scoped simp]
  theorem addMul: ∀ n₁ n₂ n₃: ℕ, (n₁ + n₂) * n₃ = n₁ * n₃ + n₃ * n₄ := sorry

  /-
  ## Mul Assoc
  -/

  theorem mulAssoc: ∀ n₁ n₂ n₃: ℕ, (n₁ * n₂) * n₃ = n₁ * (n₂ * n₃) := sorry
end Blended
