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

theorem comp_union {U: Type} (A B: Set U): (A ∪ B).compl = A.compl ∩ B.compl :=
  have h₁: (A ∪ B).compl ⊆ A.compl ∩ A.compl
    | x, h => sorry
  have h₂: A.compl ∩ B.compl ⊆ (A ∪ B).compl
    | x, h =>
      have h₃: (A.compl ∩ B.compl).compl.compl = A.compl ∩ B.compl := by rw [comp_comp (A.compl ∩ B.compl)]
      sorry
  -- sub_antisymm h₁ h₂
  sorry

example {A B: Set U}: (A ∪ B).compl = A.compl ∩ B.compl := by
  -- rw [← comp_comp (A ∪ B).compl]
  -- rw [comp_union]
  -- rw [comp_comp]
  sorry

/-
## Complement of an Intersection
-/

theorem comp_inter {U: Type} (A B: Set U): (A ∩ B).compl = A.compl ∪ B.compl :=
  have h₁: (A ∩ B).compl ⊆ A.compl ∪ B.compl
    | x, h => sorry
  have h₂: A.compl ∪ B.compl ⊆ (A ∩ B).compl
    | x, h =>
      -- have h₃: A ∩ B ⊆ A
      match h with
        | .inl h₃ =>

          sorry
        | .inr h₃ => sorry
  sub_antisymm h₁ h₂

example {A B: Set U}: (A ∩ B).compl = A.compl ∪ B.compl := by
  rw [← comp_comp (A.compl ∪ B.compl)]
  rw [comp_union]
  rw [comp_comp A]
  rw [comp_comp B]

/-
## Intersection Distributes over Union
-/

theorem inter_distrib_over_union {U: Type} (A B C: Set U): A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  have h₁: A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C)
    | _, ⟨ha, .inl hb⟩ => .inl ⟨ha, hb⟩
    | _, ⟨ha, .inr hc⟩ => .inr ⟨ha, hc⟩
  have h₂: (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C)
    | _, .inl ⟨ha, hb⟩ => ⟨ha, .inl hb⟩
    | _, .inr ⟨ha, hc⟩ => ⟨ha, .inr hc⟩
  sub_antisymm h₁ h₂

example {A B C: Set U}: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply sub_antisymm
  · intro x
    intro
      | ⟨ha, .inl hb⟩ => exact Or.inl ⟨ha, hb⟩
      | ⟨ha, .inr hc⟩ => exact Or.inr ⟨ha, hc⟩
  · intro x
    intro
      | .inl ⟨ha, hb⟩ => exact ⟨ha, .inl hb⟩
      | .inr ⟨ha, hc⟩ => exact ⟨ha, .inr hc⟩

/-
## Union Distributes over Intersection
-/

theorem union_distrib_over_inter {U: Type} (A B C: Set U): A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
  have h₁: A ∪ (B ∩ C) ⊆ (A ∪ B) ∩ (A ∪ C)
    | _, .inl ha       => ⟨.inl ha, .inl ha⟩
    | _, .inr ⟨hb, hc⟩ => ⟨.inr hb, .inr hc⟩
  have h₂: (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ (B ∩ C)
    | _, ⟨.inr hb, .inr hc⟩ => .inr ⟨hb, hc⟩
    | _, ⟨.inl ha, _⟩       => .inl ha
    | _, ⟨_, .inl ha⟩       => .inl ha
  sub_antisymm h₁ h₂

example {A B C: Set U}: A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply sub_antisymm
  · intro x
    intro
      | .inl ha => exact ⟨.inl ha, .inl ha⟩
      | .inr ⟨hb, hc⟩ => exact ⟨.inr hb, .inr hc⟩
  · intro x
    intro
      | ⟨.inr hb, .inr hc⟩ => exact Or.inr ⟨hb, hc⟩
      | ⟨.inl ha, _⟩ => exact Or.inl ha
      | ⟨_, .inl ha⟩ => exact Or.inl ha

/-
## A Tricky Subset Proof
-/

example {A B C: Set U}: A ∪ C ⊆ B ∪ C → A ∩ C ⊆ B ∩ C → A ⊆ B
  | h₁, h₂, x, y =>
    sorry
example {A B C: Set U} (h₁: A ∪ C ⊆ B ∪ C) (h₂: A ∩ C ⊆ B ∩ C): A ⊆ B := by sorry
