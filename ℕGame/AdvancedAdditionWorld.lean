/-
# Advanced Addition World
-/

import Mathlib.Tactic.Relation.Symm

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»
import «ℕGame».«ImplicationWorld»

namespace Term
  /-
  ## n ≠ n.succ
  -/

  theorem neSuccSelf: ∀ n: ℕ, n ≠ n.succ
    | .zero, h₁ =>
      have h₂: 0 ≠ (0: ℕ).succ := zeroNeSucc 0
      absurd h₁ h₂
    | .succ n, h =>
      have h₁: n = n.succ := succInj n n.succ h
      have h₂: n ≠ n.succ := neSuccSelf n
      absurd h₁ h₂

  /-
  ## Add Right Cancel
  -/

  theorem addRightCancel: ∀ n₁ n₂ n₃: ℕ, n₁ + n₃ = n₂ + n₃ → n₁ = n₂
    | n₁, n₂, .zero, h =>
      calc n₁
        _ = n₁ + ℕ.zero := Eq.symm (addZero n₁)
        _ = n₂ + ℕ.zero := h
        _ = n₂          := addZero n₂
    | n₁, n₂, .succ n₃, h =>
      have h₁: n₁ + n₃ = n₂ + n₃ :=
        have h₂: (n₁ + n₃).succ = (n₂ + n₃).succ :=
          calc (n₁ + n₃).succ
            _ = n₁ + n₃.succ   := Eq.symm (addSucc n₁ n₃)
            _ = n₂ + n₃.succ   := h
            _ = (n₂ + n₃).succ := addSucc n₂ n₃
        succInj (n₁ + n₃) (n₂ + n₃) h₂
      addRightCancel n₁ n₂ n₃ h₁

  /-
  ## Add Left Cancel
  -/

  theorem addLeftCancel (n₁ n₂ n₃: ℕ) (h: n₁ + n₂ = n₁ + n₃): n₂ = n₃ :=
    have h₁: n₂ + n₁ = n₃ + n₁ :=
      calc n₂ + n₁
        _ = n₁ + n₂ := addComm n₂ n₁
        _ = n₁ + n₃ := h
        _ = n₃ + n₁ := addComm n₁ n₃
    addRightCancel n₂ n₃ n₁ h₁

  /-
  ## Add Left = Self
  -/

  theorem addLeftEqSelf: ∀ n₁ n₂: ℕ, n₁ + n₂ = n₂ → n₁ = (0: ℕ)
    | n₁, .zero, h =>
      calc n₁
        _ = n₁ + 0 := Eq.symm (addZero n₁)
        _ = 0      := h
    | n₁, .succ n₂, h =>
      have h₁: (n₁ + n₂).succ = n₂.succ :=
        calc (n₁ + n₂).succ
          _ = n₁ + n₂.succ := Eq.symm (addSucc n₁ n₂)
          _ = n₂.succ      := h
      have h₂: n₁ + n₂ = n₂ := succInj (n₁ + n₂) n₂ h₁
      addLeftEqSelf n₁ n₂ h₂

  /-
  ## Add Right = Self
  -/

  theorem addRightEqSelf (n₁ n₂: ℕ) (h: n₁ + n₂ = n₁): n₂ = (0: ℕ) :=
    have h₁: n₂ + n₁ = n₁ :=
      calc n₂ + n₁
        _ = n₁ + n₂ := addComm n₂ n₁
        _ = n₁      := h
    addLeftEqSelf n₂ n₁ h₁

  /-
  ## a + b = 0 → a = 0
  -/

  theorem eqZeroOfAddRightEqZero: ∀ n₁ n₂: ℕ, n₁ + n₂ = (0: ℕ) → n₁ = (0: ℕ)
    | n₁, .zero, h =>
      calc n₁
        _ = n₁ + ℕ.zero := Eq.symm (addZero n₁)
        _ = 0           := h
    | n₁, .succ n₂, h =>
      have h₁: 0 = (n₁ + n₂).succ :=
        calc 0
          _ = n₁ + n₂.succ   := Eq.symm h
          _ = (n₁ + n₂).succ := addSucc n₁ n₂
      have h₂: 0 ≠ (n₁ + n₂).succ := zeroNeSucc (n₁ + n₂)
      absurd h₁ h₂

  /-
  ## a + b = 0 ⇒ b = 0
  -/

  theorem eqZeroOfAddLeftEqZero (n₁ n₂: ℕ) (h: n₁ + n₂ = (0: ℕ)): n₂ = (0: ℕ) :=
    have h₁: n₂ + n₁ = 0 :=
      calc n₂ + n₁
        _ = n₁ + n₂ := addComm n₂ n₁
        _ = 0       := h
    eqZeroOfAddRightEqZero n₂ n₁ h₁
end Term

namespace Tactic
  /-
  ## n ≠ n.succ
  -/

  @[scoped simp]
  theorem neSuccSelf (n: ℕ): n ≠ n.succ := by
    induction n with
      | zero => apply zeroNeSucc
      | succ n ihₙ =>
        intro h
        have h₂: n = n.succ := by
          rw [succInj n.succ]
          apply Eq.symm
          exact h
        contradiction

  /-
  ## Add Right Cancel
  -/

  @[scoped simp]
  theorem addRightCancel (n₁ n₂ n₃: ℕ): n₁ + n₃ = n₂ + n₃ → n₁ = n₂ := by
    intro h
    induction n₃ with
      | zero =>
        simp at h
        exact h
      | succ n₃ ihn₃ =>
        simp at h
        have h₂: n₁ + n₃ = n₂ + n₃ := by
          rw [succInj (n₁ + n₃) (n₂ + n₃)]
          simp
          exact h
        apply ihn₃ h₂

  /-
  ## Add Left Cancel
  -/

  @[scoped simp]
  theorem addLeftCancel (n₁ n₂ n₃: ℕ): n₁ + n₂ = n₁ + n₃ → n₂ = n₃ := by
    repeat rw [addComm n₁]
    exact addRightCancel n₂ n₃ n₁

  /-
  ## Add Left = Self
  -/

  @[scoped simp]
  theorem addLeftEqSelf (n₁ n₂: ℕ): n₁ + n₂ = n₂ → n₁ = (0: ℕ) := by
    intro h
    induction n₂ with
      | zero =>
        simp at h
        exact h
      | succ n₂ ihn₂ =>
        have h₂: n₁ + n₂ = n₂ := by
          rw [addSucc] at h
          apply succInj
          exact h
        apply ihn₂
        exact h₂

  /-
  ## Add Right = Self
  -/

  @[scoped simp]
  theorem addRightEqSelf (n₁ n₂: ℕ): n₁ + n₂ = n₁ → n₂ = (0: ℕ) := by
    rw [addComm]
    exact addLeftEqSelf n₂ n₁

  /-
  ## a + b = 0 → a = 0
  -/

  @[scoped simp]
  theorem eqZeroOfAddRightEqZero (n₁ n₂: ℕ): n₁ + n₂ = (0: ℕ) → n₁ = (0: ℕ) := by
    intro h
    cases n₂ with
      | zero =>
        simp at h
        exact h
      | succ n₂ =>
        have h₁: 0 ≠ (n₁ + n₂).succ := zeroNeSucc (n₁ + n₂)
        rw [addSucc] at h
        symm at h
        contradiction

  /-
  ## a + b = 0 ⇒ b = 0
  -/

  @[scoped simp]
  theorem eqZeroOfAddLeftEqZero (n₁ n₂: ℕ): n₁ + n₂ = (0: ℕ) → n₂ = (0: ℕ) := by
    rw [addComm]
    apply eqZeroOfAddRightEqZero
end Tactic

namespace Blended
  /-
  ## n ≠ n.succ
  -/

  @[scoped simp]
  theorem neSuccSelf: ∀ n: ℕ, n ≠ n.succ
    | .zero, h₁ => by contradiction
    | .succ n, h =>
      have h₁: n = n.succ := succInj n n.succ h
      have h₂: n ≠ n.succ := neSuccSelf n
      by contradiction

  /-
  ## Add Right Cancel
  -/

  @[scoped simp]
  theorem addRightCancel: ∀ n₁ n₂ n₃: ℕ, n₁ + n₃ = n₂ + n₃ → n₁ = n₂
    | n₁, n₂, .zero, h =>
      calc n₁
        _ = n₁ + ℕ.zero := by simp
        _ = n₂ + ℕ.zero := h
        _ = n₂          := by simp
    | n₁, n₂, .succ n₃, h =>
      have h₁: n₁ + n₃ = n₂ + n₃ :=
        have h₂: (n₁ + n₃).succ = (n₂ + n₃).succ :=
          calc (n₁ + n₃).succ
            _ = n₁ + n₃.succ   := by simp
            _ = n₂ + n₃.succ   := h
            _ = (n₂ + n₃).succ := by simp
        succInj (n₁ + n₃) (n₂ + n₃) h₂
      addRightCancel n₁ n₂ n₃ h₁

  /-
  ## Add Left Cancel
  -/

  @[scoped simp]
  theorem addLeftCancel (n₁ n₂ n₃: ℕ) (h: n₁ + n₂ = n₁ + n₃): n₂ = n₃ :=
    have h₁: n₂ + n₁ = n₃ + n₁ :=
      calc n₂ + n₁
        _ = n₁ + n₂ := by simp
        _ = n₁ + n₃ := h
        _ = n₃ + n₁ := by simp
    addRightCancel n₂ n₃ n₁ h₁

  /-
  ## Add Left = Self
  -/

  theorem addLeftEqSelf: ∀ n₁ n₂: ℕ, n₁ + n₂ = n₂ → n₁ = (0: ℕ)
    | n₁, .zero, h =>
      calc n₁
        _ = n₁ + 0 := by simp
        _ = 0      := h
    | n₁, .succ n₂, h =>
      have h₁: (n₁ + n₂).succ = n₂.succ :=
        calc (n₁ + n₂).succ
          _ = n₁ + n₂.succ := by simp
          _ = n₂.succ      := h
      have h₂: n₁ + n₂ = n₂ := succInj (n₁ + n₂) n₂ h₁
      addLeftEqSelf n₁ n₂ h₂

  /-
  ## Add Right = Self
  -/

  @[scoped simp]
  theorem addRightEqSelf (n₁ n₂: ℕ) (h: n₁ + n₂ = n₁): n₂ = (0: ℕ) :=
    have h₁: n₂ + n₁ = n₁ :=
      calc n₂ + n₁
        _ = n₁ + n₂ := by simp
        _ = n₁      := h
    addLeftEqSelf n₂ n₁ h₁

  /-
  ## a + b = 0 → a = 0
  -/

  @[scoped simp]
  theorem eqZeroOfAddRightEqZero: ∀ n₁ n₂: ℕ, n₁ + n₂ = (0: ℕ) → n₁ = (0: ℕ)
    | n₁, .zero, h =>
      calc n₁
        _ = n₁ + ℕ.zero := by simp
        _ = 0           := h
    | n₁, .succ n₂, h =>
      have: 0 = (n₁ + n₂).succ :=
        calc 0
          _ = n₁ + n₂.succ   := by rw [h]
          _ = (n₁ + n₂).succ := by simp
      have: 0 ≠ (n₁ + n₂).succ := zeroNeSucc (n₁ + n₂)
      by contradiction

  /-
  ## a + b = 0 ⇒ b = 0
  -/

  @[scoped simp]
  theorem eqZeroOfAddLeftEqZero (n₁ n₂: ℕ) (h: n₁ + n₂ = (0: ℕ)): n₂ = (0: ℕ) :=
    have h₁: n₂ + n₁ = 0 :=
      calc n₂ + n₁
        _ = n₁ + n₂ := by simp
        _ = 0       := h
    eqZeroOfAddRightEqZero n₂ n₁ h₁
end Blended
