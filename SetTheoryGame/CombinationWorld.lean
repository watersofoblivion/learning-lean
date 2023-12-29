/-
# Combination World
-/

import «SetTheoryGame».«SubsetWorld»
import «SetTheoryGame».«ComplementWorld»
import «SetTheoryGame».«IntersectionWorld»
import «SetTheoryGame».«UnionWorld»

/-
## Complement of a Union
-/

theorem comp_union (A B: Set U): (A ∪ B).compl = A.compl ∩ B.compl :=
  have h₁: (A ∪ B).compl ⊆ A.compl ∩ A.compl
    | x, h => sorry
  have h₂: A.compl ∩ B.compl ⊆ (A ∪ B).compl
    | x, h => sorry
  -- sub_antisymm h₁ h₂
  sorry

example {A B: Set U}: (A ∪ B).compl = A.compl ∩ B.compl := by
  apply sub_antisymm
  · intro x h
    sorry
  · intro x h
    sorry

/-
## Complement of an Intersection
-/

theorem comp_inter (A B: Set U): (A ∩ B).compl = A.compl ∪ B.compl := sorry
example {A B: Set U}: (A ∩ B).compl = A.compl ∪ B.compl := by sorry

/-
## Intersection Distributes over Union
-/

theorem inter_distrib_over_union (A B C: Set U): A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := sorry
example {A B C: Set U}: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by sorry

/-
## Union Distributes over Intersection
-/

theorem union_distrib_over_inter (A B C: Set U): A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := sorry
example {A B C: Set U}: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by sorry

/-
## A Tricky Subset Proof
-/

example {A B C: Set U}: A ∪ C ⊆ B ∪ C → A ∩ C ⊆ B ∩ C → A ⊆ B := sorry
example {A B C: Set U} (h₁: A ∪ C ⊆ B ∪ C) (h₂: A ∩ C ⊆ B ∩ C): A ⊆ B := by sorry
