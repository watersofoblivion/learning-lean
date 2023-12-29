/-
# Subset World
-/

import Mathlib.Init.Set

/-
## The Exact Tactic
-/

example {x: U} {A: Set U} (h: x ∈ A): x ∈ A := h
example {x: U} {A: Set U} (h: x ∈ A): x ∈ A := by
  exact h

/-
## A Subset Hypothesis
-/

example {x: U} {A B: Set U} (h₁: A ⊆ B) (h₂: x ∈ A): x ∈ B := h₁ h₂
example {x: U} {A B: Set U} (h₁: A ⊆ B) (h₂: x ∈ A): x ∈ B := by
  exact h₁ h₂

/-
## The Have Tactic
-/

example {x: U} {A B C: Set U} (h₁: A ⊆ B) (h₂: B ⊆ C) (h₃: x ∈ A): x ∈ C :=
  have h₄: x ∈ B := h₁ h₃
  h₂ h₄

example {x: U} {A B C: Set U} (h₁: A ⊆ B) (h₂: B ⊆ C) (h₃: x ∈ A): x ∈ C := by
  have h₄: x ∈ B := h₁ h₃
  exact h₂ h₄

/-
## Implication
-/

example {x: U} {A B C: Set U} (h₁: A ⊆ B) (h₂: x ∈ B → x ∈ C): x ∈ A → x ∈ C
  | h₃ =>
    have h₄: x ∈ B := h₁ h₃
    h₂ h₄

example {x: U} {A B C: Set U} (h₁: A ⊆ B) (h₂: x ∈ B → x ∈ C): x ∈ A → x ∈ C := by
  intro h₃
  have h₄: x ∈ B := h₁ h₃
  exact h₂ h₄

/-
## Subset is Reflexive
-/

theorem sub_refl (A: Set U): A ⊆ A
  | _, h => h

example {A: Set U}: A ⊆ A := by
  intro x h
  exact h

/-
## Subset is Transitive
-/

theorem sub_trans {A B C: Set U} (h₁: A ⊆ B) (h₂: B ⊆ C): A ⊆ C
  | x, h₃ =>
    have h₄: x ∈ B := h₁ h₃
    h₂ h₄

example {A B C: Set U} (h₁: A ⊆ B) (h₂: B ⊆ C): A ⊆ C := by
  intro x h₃
  have h₄: x ∈ B := h₁ h₃
  exact h₂ h₄
