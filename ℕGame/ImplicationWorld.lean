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

  example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = (37: ℕ)) (_: (3: ℕ) * n₁ + n₃ = (42: ℕ)): n₁ + n₂ = (37: ℕ) := h₁

  /-
  ## `exact` practice
  -/

  example (n₁: ℕ) (h: (0: ℕ) + n₁ = (0: ℕ) + n₂ + (2: ℕ)): n₁ = n₂ + (2: ℕ) :=
    have h₁: ℕ.add (0 + n₂) = ℕ.add n₂ := congrArg ℕ.add (zeroAdd n₂)
    calc n₁
      _ = 0 + n₁     := Eq.symm (zeroAdd n₁)
      _ = 0 + n₂ + 2 := h
      _ = n₂ + 2     := congrFun h₁ 2

  /-
  ## The `apply` tactic
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = (37: ℕ)) (h₂: n₁ = (37: ℕ) → n₂ = (42: ℕ)): n₂ = 42 :=
    h₂ h₁

  /-
  ## `succInj`: The successor function is injective
  -/

  example (n: ℕ) (h: n + 1 = (4: ℕ)): n = (3: ℕ) :=
    have h₁: n.succ = (3: ℕ).succ :=
      calc n.succ
        _ = n + 1       := succEqAddOne n
        _ = 4           := h
        _ = (3: ℕ).succ := fourSuccOfThree
    succInj n 3 h₁

  /-
  ## Arguing backwards
  -/

  -- Same as previous

  /-
  ## `intro`
  -/

  example (n: ℕ): n = (37: ℕ) → n = (37: ℕ)
    | h => h

  /-
  ## `intro` practice
  -/

  example (n₁: ℕ) (h: n₁ + (1: ℕ) = n₂ + (1: ℕ)): n₁ = n₂ :=
    have h₁: n₁.succ = n₂.succ :=
      calc n₁.succ
        _ = n₁ + 1 := succEqAddOne n₁
        _ = n₂ + 1 := h
        _ = n₂.succ := Eq.symm (succEqAddOne n₂)
    succInj n₁ n₂ h₁

  /--
  ## ≠
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False :=
    absurd h₁ h₂

  /--
  ## Zero ≠ Succ
  -/

  theorem zeroNeOne: (0: ℕ) ≠ (1: ℕ)
    | h => absurd h (zeroNeSucc ℕ.zero)

  /--
  ## 1 ≠ 0
  -/

  theorem oneNeZero: (1: ℕ) ≠ (0: ℕ)
    | h => zeroNeOne (Eq.symm h)

  /--
  ## 2 + 2 ≠ 5
  -/

  example: (2: ℕ) + (2: ℕ) ≠ (5: ℕ)
    | h => sorry
end Term

namespace Tactic
  /-
  ## The `exact` tactic
  -/

  example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = (37: ℕ)) (_: (3: ℕ) * n₁ + n₃ = (42: ℕ)): n₁ + n₂ = (37: ℕ) := by
    exact h₁

  /-
  ## `exact` practice
  -/

  example (n₁: ℕ) (h: (0: ℕ) + n₁ = (0: ℕ) + n₂ + (2: ℕ)): n₁ = n₂ + (2: ℕ) := by
    simp [add0L] at h
    exact h

  /-
  ## The `apply` tactic
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = (37: ℕ)) (h₂: n₁ = (37: ℕ) → n₂ = (42: ℕ)): n₂ = (42: ℕ) := by
    apply h₂ h₁

  /-
  ## `succInj`: The successor function is injective
  -/

  example (n: ℕ) (h: n + (1: ℕ) = (4: ℕ)): n = (3: ℕ) := by
    rw [fourSuccOfThree, ← succEqAddOne] at h
    apply succInj
    exact h

  /-
  ## Arguing backwards
  -/

  example (n: ℕ) (h: n + (1) = (4: ℕ)): n = (3: ℕ) := by
    apply succInj
    rw [succEqAddOne, ← fourSuccOfThree]
    exact h

  /-
  ## `intro`
  -/

  example (n: ℕ): n = (37: ℕ) → n = (37: ℕ) := by
    intro h
    apply h

  /-
  ## `intro` practice
  -/

  example (n₁: ℕ): n₁ + (1: ℕ) = n₂ + (1: ℕ) → n₁ = n₂ := by
    intro h
    repeat rw [← succEqAddOne] at h
    apply succInj
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

  @[scoped simp]
  theorem zeroNeOne: (0: ℕ) ≠ (1: ℕ) := by
    intro h
    rw [oneSuccOfZero] at h
    apply zeroNeSucc
    exact h

  /-
  ## 1 ≠ 0
  -/

  @[scoped simp]
  theorem oneNeZero: (1: ℕ) ≠ (0: ℕ) := by
    symm
    exact zeroNeOne

  /-
  ## 2 + 2 ≠ 5
  -/

  example: (2: ℕ) + (2: ℕ) ≠ (5: ℕ) := by
    intro h
    repeat rw [fiveSuccOfFour, fourSuccOfThree, threeSuccOfTwo, twoSuccOfOne, oneSuccOfZero] at h
    simp at h
end Tactic

namespace Blended
  /-
  ## The `exact` tactic
  -/

  example (n₁ n₂ n₃: ℕ) (h₁: n₁ + n₂ = (37: ℕ)) (_: (3: ℕ) * n₁ + n₃ = (42: ℕ)): n₁ + n₂ = (37: ℕ) := h₁

  /-
  ## `exact` practice
  -/

  example (n₁: ℕ) (h: (0: ℕ) + n₁ = (0: ℕ) + n₂ + (2: ℕ)): n₁ = n₂ + (2: ℕ) :=
    calc n₁
      _ = ℕ.zero + n₁     := by simp
      _ = ℕ.zero + n₂ + 2 := h
      _ = n₂ + 2          := by simp

  /-
  ## The `apply` tactic
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = (37: ℕ)) (h₂: n₁ = (37: ℕ) → n₂ = (42: ℕ)): n₂ = (42: ℕ) :=
    h₂ h₁

  /-
  ## `succInj`: The successor function is injective
  -/

  example (n: ℕ) (h: n + (1: ℕ) = (4: ℕ)): n = (3: ℕ) :=
    have h₁: n.succ = (3: ℕ).succ :=
      calc n.succ
        _ = n + 1       := by rw [succEqAddOne]
        _ = 4           := h
        _ = (3: ℕ).succ := by rw [fourSuccOfThree]
    succInj n 3 h₁

  /-
  ## Arguing backwards
  -/

  -- Same as previous

  /-
  ## `intro`
  -/

  example (n: ℕ): n = (37: ℕ) → n = (37: ℕ)
    | h => h

  /-
  ## `intro` practice
  -/

  example (n₁: ℕ) (h: n₁ + (1: ℕ) = n₂ + (1: ℕ)): n₁ = n₂ :=
    have h₁: n₁.succ = n₂.succ :=
      calc n₁.succ
        _ = n₁ + 1 := by rw [succEqAddOne]
        _ = n₂ + 1 := h
        _ = n₂.succ := by rw [succEqAddOne]
    succInj n₁ n₂ h₁

  /-
  ## ≠
  -/

  example (n₁ n₂: ℕ) (h₁: n₁ = n₂) (h₂: n₁ ≠ n₂): False := by
    contradiction

  /-
  ## Zero ≠ Succ
  -/

  @[scoped simp]
  theorem zeroNeOne: (0: ℕ) ≠ (1: ℕ)
    | _ => by contradiction

  /-
  ## 1 ≠ 0
  -/

  @[scoped simp]
  theorem oneNeZero: (1: ℕ) ≠ (0: ℕ)
    | _ => by contradiction

  /-
  ## 2 + 2 ≠ 5
  -/

  example: (2: ℕ) + (2: ℕ) ≠ (5: ℕ) := sorry
end Blended
