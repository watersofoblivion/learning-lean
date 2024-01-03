/-
# Implication World
-/

import Mathlib.Tactic.Relation.Symm

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»
import «ℕGame».«AdditionWorld»

namespace Term
  /-
  ## The `exact` tactic
  -/

  example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = 37) (_: 3 * n₁ + n₃ = 42): n₁ + n₂ = 37 := h₁

  /-
  ## `exact` practice
  -/

  example (n₁: ℕ) (h: 0 + n₁ = 0 + n₂ + 2): n₁ = n₂ + 2 :=
    have h₁: ℕ.add (0 + n₂) = ℕ.add n₂ := congrArg ℕ.add (zeroAdd n₂)
    calc n₁
      _ = 0 + n₁     := Eq.symm (zeroAdd n₁)
      _ = 0 + n₂ + 2 := h
      _ = n₂ + 2     := congrFun h₁ 2

  /-
  ## The `apply` tactic
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = 37) (h₂: n₁ = 37 → n₂ = 42): n₂ = 42 :=
    h₂ h₁

  /-
  ## `succInj`: The successor function is injective
  -/

  example (n: ℕ) (h: n + 1 = 4): n = 3 :=
    have h₁: n.succ = (3: ℕ).succ :=
      calc n.succ
        _ = n + 1       := succEqAddOne n
        _ = 4           := h
        _ = (3: ℕ).succ := ℕ.fourSuccOfThree
    ℕ.succInj n 3 h₁

  /-
  ## Arguing backwards
  -/

  -- Same as previous

  /-
  ## `intro`
  -/

  example (n: ℕ): n = 37 → n = 37
    | h => h

  /-
  ## `intro` practice
  -/

  example (n₁: ℕ) (h: n₁ + 1 = n₂ + 1): n₁ = n₂ :=
    have h₁: n₁.succ = n₂.succ :=
      calc n₁.succ
        _ = n₁ + 1 := succEqAddOne n₁
        _ = n₂ + 1 := h
        _ = n₂.succ := Eq.symm (succEqAddOne n₂)
    ℕ.succInj n₁ n₂ h₁

  /--
  ## ≠
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False :=
    absurd h₁ h₂

  /--
  ## Zero ≠ Succ
  -/

  theorem zeroNeOne: (0: ℕ) ≠ 1
    | h => absurd h (ℕ.zeroNeSucc ℕ.zero)

  /--
  ## 1 ≠ 0
  -/

  theorem oneNeZero: (1: ℕ) ≠ 0
    | h => zeroNeOne (Eq.symm h)

  /--
  ## 2 + 2 ≠ 5
  -/

  example: (2: ℕ) + 2 ≠ 5
    | h => sorry
end Term

namespace Tactic
  /-
  ## The `exact` tactic
  -/

  example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = 37) (_: 3 * n₁ + n₃ = 42): n₁ + n₂ = 37 := by
    exact h₁

  /-
  ## `exact` practice
  -/

  example (n₁: ℕ) (h: 0 + n₁ = 0 + n₂ + 2): n₁ = n₂ + 2 := by
    simp [add0L] at h
    exact h

  /-
  ## The `apply` tactic
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = 37) (h₂: n₁ = 37 → n₂ = 42): n₂ = 42 := by
    apply h₂ h₁

  /-
  ## `succInj`: The successor function is injective
  -/

  example (n: ℕ) (h: n + 1 = 4): n = 3 := by
    rw [ℕ.fourSuccOfThree, ← succEqAddOne] at h
    apply ℕ.succInj
    exact h

  /-
  ## Arguing backwards
  -/

  example (n: ℕ) (h: n + 1 = 4): n = 3 := by
    apply ℕ.succInj
    rw [succEqAddOne, ← ℕ.fourSuccOfThree]
    exact h

  /-
  ## `intro`
  -/

  example (n: ℕ): n = 37 → n = 37 := by
    intro h
    apply h

  /-
  ## `intro` practice
  -/

  example (n₁: ℕ): n₁ + 1 = n₂ + 1 → n₁ = n₂ := by
    intro h
    repeat rw [← succEqAddOne] at h
    apply ℕ.succInj
    exact h

  /-
  ## ≠
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False := by
    apply h₂ h₁

  example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False := by
    contradiction

  /-
  ## Zero ≠ Succ
  -/

  @[local simp]
  theorem zeroNeOne: (0: ℕ) ≠ 1 := by
    intro h
    rw [ℕ.oneSuccOfZero] at h
    apply ℕ.zeroNeSucc
    exact h

  /-
  ## 1 ≠ 0
  -/

  @[local simp]
  theorem oneNeZero: (1: ℕ) ≠ 0 := by
    symm
    exact zeroNeOne

  /-
  ## 2 + 2 ≠ 5
  -/

  example: (2: ℕ) + 2 ≠ 5 := by
    intro h
    repeat rw [ℕ.fiveSuccOfFour, ℕ.fourSuccOfThree, ℕ.threeSuccOfTwo, ℕ.twoSuccOfOne, ℕ.oneSuccOfZero] at h
    repeat rw [ℕ.addSucc] at h
    rw [ℕ.addZero] at h
    repeat rw [ℕ.zeroNeSucc] at h
    -- apply ℕ.succInj at h -- Equivalent outside the NNG?
    sorry
end Tactic

namespace Blended
  /-
  ## The `exact` tactic
  -/

  example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = 37) (_: 3 * n₁ + n₃ = 42): n₁ + n₂ = 37 := h₁

  /-
  ## `exact` practice
  -/

  example (n₁: ℕ) (h: 0 + n₁ = 0 + n₂ + 2): n₁ = n₂ + 2 :=
    calc n₁
      _ = ℕ.zero + n₁     := by rw [zeroAdd]
      _ = ℕ.zero + n₂ + 2 := h
      _ = n₂ + 2          := by rw [zeroAdd]

  /-
  ## The `apply` tactic
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = 37) (h₂: n₁ = 37 → n₂ = 42): n₂ = 42 :=
    h₂ h₁

  /-
  ## `succInj`: The successor function is injective
  -/

  example (n: ℕ) (h: n + 1 = 4): n = 3 :=
    have h₁: n.succ = (3: ℕ).succ :=
      calc n.succ
        _ = n + 1       := by rw [succEqAddOne]
        _ = 4           := h
        _ = (3: ℕ).succ := by rw [ℕ.fourSuccOfThree]
    ℕ.succInj n 3 h₁

  /-
  ## Arguing backwards
  -/

  -- Same as previous

  /-
  ## `intro`
  -/

  example (n: ℕ): n = 37 → n = 37
    | h => h

  /-
  ## `intro` practice
  -/

  example (n₁: ℕ) (h: n₁ + 1 = n₂ + 1): n₁ = n₂ :=
    have h₁: n₁.succ = n₂.succ :=
      calc n₁.succ
        _ = n₁ + 1 := by rw [succEqAddOne]
        _ = n₂ + 1 := h
        _ = n₂.succ := by rw [succEqAddOne]
    ℕ.succInj n₁ n₂ h₁

  /-
  ## ≠
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False := by
    contradiction

  /-
  ## Zero ≠ Succ
  -/

  @[local simp]
  theorem zeroNeOne: (0: ℕ) ≠ 1
    | _ => by contradiction

  /-
  ## 1 ≠ 0
  -/

  @[local simp]
  theorem oneNeZero: (1: ℕ) ≠ 0
    | _ => by contradiction

  /-
  ## 2 + 2 ≠ 5
  -/

  example: (2: ℕ) + 2 ≠ 5 := sorry
end Blended
