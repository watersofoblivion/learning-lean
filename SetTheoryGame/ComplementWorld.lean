/-
# Complement World
-/

import Mathlib.Init.Set

import «SetTheoryGame».«SubsetWorld»

/-
## Proof by Contradiction
-/

example {A B: Set U} {x: U} (h₁: x ∈ A) (h₂: x ∉ B): ¬A ⊆ B :=
  fun h₃: A ⊆ B =>
    have h₄: x ∈ B := h₃ h₁
    absurd h₄ h₂

example {A B: Set U} {x: U} (h₁: x ∈ A) (h₂: x ∉ B): ¬A ⊆ B := by
  intro h₃
  have h₄: x ∈ B := h₃ h₁
  exact h₂ h₄

/-
## Definition of Complement
-/

theorem comp_def {x: U} {A: Set U}: x ∈ A.compl ↔ x ∉ A :=
  have mp: x ∈ A.compl → x ∉ A
    | h₁, h₂ => absurd h₂ h₁
  have mpr: x ∉ A → x ∈ A.compl
    | h₁, h₂ => absurd h₂ h₁
  ⟨mp, mpr⟩

example {x: U} {A: Set U}: x ∈ A.compl ↔ x ∉ A := by
  apply Iff.intro
  · intro h₁ h₂
    contradiction
  · intro h₁ h₂
    contradiction

/-
## Complement Subsets from Subsets
-/

theorem comp_sub_of_sub {A B: Set U} (h₁: A ⊆ B): B.compl ⊆ A.compl
  | x, h₂ => sorry

example {A B: Set U} (h₁: A ⊆ B): B.compl ⊆ A.compl := by
  intro x h₂
  rw [comp_def]
  rw [comp_def] at h₂
  intro h₃
  have h₄: x ∈ B := h₁ h₃
  contradiction

/-
## Complement of a Complement
-/

-- Provided
theorem sub_antisymm {U : Type} {A B : Set U} (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B := sorry

theorem comp_comp (A: Set U): A.compl.compl = A := sorry
example {A: Set U}: A.compl.compl = A := by sorry

/-
## Complement Subsets Equivalence
-/

example {A B: Set U}: A ⊆ B ↔ B.compl ⊆ A.compl :=
  have mp (h: A ⊆ B): B.compl ⊆ A.compl := comp_sub_of_sub h
  have mpr (h₁: B.compl ⊆ A.compl): A ⊆ B :=
    have h₂: A.compl.compl ⊆ B.compl.compl := comp_sub_of_sub h₁
    have h₃: A.compl.compl = A := comp_comp A
    have h₄: B.compl.compl = B := comp_comp B
    by
      rw [h₃, h₄] at h₂
      exact h₂
  ⟨mp, mpr⟩

example {A B: Set U}: A ⊆ B ↔ B.compl ⊆ A.compl := by
  apply Iff.intro
  · intro h₁
    apply comp_sub_of_sub
    exact h₁
  · intro h₁
    have h₂: A.compl.compl ⊆ B.compl.compl := comp_sub_of_sub h₁
    have h₃: A.compl.compl = A := comp_comp A
    have h₄: B.compl.compl = B := comp_comp B
    rw [h₃, h₄] at h₂
    exact h₂
