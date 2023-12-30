/-
# Advanced Addition World
-/

import Mathlib.Tactic.Relation.Symm

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»
import «ℕGame».«ImplicationWorld»

/--
## n ≠ n.succ
-/

theorem ℕ.neSuccSelf: ∀ n: ℕ, n ≠ n.succ
  | .zero, h₁ =>
    have h₂: 0 ≠ (0: ℕ).succ := ℕ.zeroNeSucc 0
    absurd h₁ h₂
  | .succ n, h =>
    have h₁: n = n.succ := ℕ.succInj n n.succ h
    have h₂: n ≠ n.succ := ℕ.neSuccSelf n
    absurd h₁ h₂

example (n: ℕ): n ≠ n.succ := by
  induction n with
    | zero => apply ℕ.zeroNeSucc
    | succ n ihₙ =>
      intro h
      -- apply ℕ.succInj -- at h -- Eqivalent outside the NNG?
      -- apply ihₙ h
      -- exact h
      sorry

/--
## Add Right Cancel
-/

theorem ℕ.addRightCancel: ∀ n₁ n₂ n₃: ℕ, n₁ + n₃ = n₂ + n₃ → n₁ = n₂
  | n₁, n₂, .zero, h =>
    calc n₁
      _ = n₁ + ℕ.zero := Eq.symm (ℕ.addZero n₁)
      _ = n₂ + ℕ.zero := h
      _ = n₂          := ℕ.addZero n₂
  | n₁, n₂, .succ n₃, h =>
    have h₁: n₁ + n₃ = n₂ + n₃ :=
      have h₂: (n₁ + n₃).succ = (n₂ + n₃).succ :=
        calc (n₁ + n₃).succ
          _ = n₁ + n₃.succ   := Eq.symm (ℕ.addSucc n₁ n₃)
          _ = n₂ + n₃.succ   := h
          _ = (n₂ + n₃).succ := ℕ.addSucc n₂ n₃
      ℕ.succInj (n₁ + n₃) (n₂ + n₃) h₂
    ℕ.addRightCancel n₁ n₂ n₃ h₁

example (n₁ n₂ n₃: ℕ): n₁ + n₃ = n₂ + n₃ → n₁ = n₂ := by
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

/--
## Add Left Cancel
-/

theorem ℕ.addLeftCancel (n₁ n₂ n₃: ℕ) (h: n₁ + n₂ = n₁ + n₃): n₂ = n₃ :=
  have h₁: n₂ + n₁ = n₃ + n₁ :=
    calc n₂ + n₁
      _ = n₁ + n₂ := ℕ.addComm n₂ n₁
      _ = n₁ + n₃ := h
      _ = n₃ + n₁ := ℕ.addComm n₁ n₃
  ℕ.addRightCancel n₂ n₃ n₁ h₁

example (n₁ n₂ n₃: ℕ): n₁ + n₂ = n₁ + n₃ → n₂ = n₃ := by
  repeat rw [ℕ.addComm n₁]
  exact ℕ.addRightCancel n₂ n₃ n₁

/--
## Add Left = Self
-/

theorem ℕ.addLeftEqSelf: ∀ n₁ n₂: ℕ, n₁ + n₂ = n₂ → n₁ = 0
  | n₁, .zero, h =>
    calc n₁
      _ = n₁ + 0 := Eq.symm (ℕ.addZero n₁)
      _ = 0      := h
  | n₁, .succ n₂, h =>
    have h₁: (n₁ + n₂).succ = n₂.succ :=
      calc (n₁ + n₂).succ
        _ = n₁ + n₂.succ := Eq.symm (ℕ.addSucc n₁ n₂)
        _ = n₂.succ      := h
    have h₂: n₁ + n₂ = n₂ := ℕ.succInj (n₁ + n₂) n₂ h₁
    ℕ.addLeftEqSelf n₁ n₂ h₂


example (n₁ n₂: ℕ): n₁ + n₂ = n₂ → n₁ = 0 := by
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

/--
## Add Right = Self
-/

theorem ℕ.addRightEqSelf (n₁ n₂: ℕ) (h: n₁ + n₂ = n₁): n₂ = 0 :=
  have h₁: n₂ + n₁ = n₁ :=
    calc n₂ + n₁
      _ = n₁ + n₂ := ℕ.addComm n₂ n₁
      _ = n₁      := h
  ℕ.addLeftEqSelf n₂ n₁ h₁

example (n₁ n₂: ℕ): n₁ + n₂ = n₁ → n₂ = 0 := by
  rw [ℕ.addComm]
  exact ℕ.addLeftEqSelf n₂ n₁

/--
## a + b = 0 → a = 0
-/

theorem ℕ.eqZeroOfAddRightEqZero: ∀ n₁ n₂: ℕ, n₁ + n₂ = 0 → n₁ = 0
  | n₁, .zero, h =>
    calc n₁
      _ = n₁ + ℕ.zero := Eq.symm (ℕ.addZero n₁)
      _ = 0           := h
  | n₁, .succ n₂, h =>
    have h₁: 0 = (n₁ + n₂).succ :=
      calc 0
        _ = n₁ + n₂.succ   := Eq.symm h
        _ = (n₁ + n₂).succ := ℕ.addSucc n₁ n₂
    have h₂: 0 ≠ (n₁ + n₂).succ := ℕ.zeroNeSucc (n₁ + n₂)
    absurd h₁ h₂

example (n₁ n₂: ℕ): n₁ + n₂ = 0 → n₁ = 0 := by
  intro h
  cases n₂ with
    | zero =>
      rw [ℕ.addZero] at h
      exact h
    | succ n₂ =>
      have h₁: 0 ≠ (n₁ + n₂).succ := ℕ.zeroNeSucc (n₁ + n₂)
      rw [ℕ.addSucc] at h
      symm at h
      contradiction

/--
## a + b = 0 ⇒ b = 0
-/

theorem ℕ.eqZeroOfAddLeftEqZero (n₁ n₂: ℕ) (h: n₁ + n₂ = 0): n₂ = 0 :=
  have h₁: n₂ + n₁ = 0 :=
    calc n₂ + n₁
      _ = n₁ + n₂ := ℕ.addComm n₂ n₁
      _ = 0       := h
  ℕ.eqZeroOfAddRightEqZero n₂ n₁ h₁

example (n₁ n₂: ℕ): n₁ + n₂ = 0 → n₂ = 0 := by
  rw [ℕ.addComm]
  apply ℕ.eqZeroOfAddRightEqZero
