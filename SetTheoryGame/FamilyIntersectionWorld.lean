/-
# Family Intersection World
-/

import Mathlib.Data.Set.Lattice

import «SetTheoryGame».«SubsetWorld»
import «SetTheoryGame».«ComplementWorld»
import «SetTheoryGame».«IntersectionWorld»
import «SetTheoryGame».«UnionWorld»

theorem fam_inter_def {U: Type} {x: U} {F: Set (Set U)}: x ∈ ⋂₀ F ↔ ∀ S ∈ F, x ∈ S := sorry
theorem pair_def {U : Type} {S A B: Set U} : S ∈ ({A, B}: Set (Set U)) ↔ S = A ∨ S = B := sorry

/-
## Family Intersection is Subset
-/

example {A: Set U} {F: Set (Set U)} (h₁: A ∈ F): ⋂₀ F ⊆ A := by
  intro x h₂
  rw [fam_inter_def] at h₂
  have h₂A: A ∈ F → x ∈ A := h₂ A
  exact h₂A h₁

/-
## Intersection of larger family is smaller
-/

example (F G: Set (Set U)) (h₁: F ⊆ G): ⋂₀ G ⊆ ⋂₀ F := by
  intro x h₂
  rw [fam_inter_def]
  intro y z
  have h₃: y ∈ G := h₁ z
  exact h₂ y h₃

/-
## Intersections of a Pair
-/

theorem inter_def {U : Type} (x : U) (A B : Set U) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := sorry



example (A B: Set U): A ∩ B = ⋂₀ {A, B} := by
  ext
  apply Iff.intro
  · intro h₁
    rw [fam_inter_def]
    intro z h₂
    sorry
  · intro h₁
    rw [inter_def]
    apply And.intro
    · rw [fam_inter_def] at h₁
      apply h₁
      sorry
    · rw [fam_inter_def] at h₁
      apply h₁

      sorry
    -- rw [inter_def]


/-
## Intersection of a Union of Families
-/

example (F G: Set (Set U)): ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  ext
  apply Iff.intro
  · intro h
    rw [fam_inter_def] at h
    sorry
  · sorry
