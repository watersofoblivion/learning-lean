/-
# Union World
-/

import «SetTheoryGame».«SubsetWorld»
import «SetTheoryGame».«ComplementWorld»
import «SetTheoryGame».«IntersectionWorld»

/-
## Or
-/

example {x: U} {A B: Set U}: x ∈ A → x ∈ A ∪ B
  | h => .inl h

example {x: U} {A B: Set U} (h: x ∈ A): x ∈ A ∪ B := by
  exact Or.inl h

/-
## Subset of a Union
-/

example {A B: Set U}: B ⊆ A ∪ B
  | _, h => Or.inr h

example {A B: Set U}: B ⊆ A ∪ B := by
  intro x h
  exact Or.inr h

/-
## Proof by Cases
-/

example {A B C: Set U}: A ⊆ C → B ⊆ C → A ∪ B ⊆ C
  | hac, _, _, .inl h => hac h
  | _, hbc, _, .inr h => hbc h

example {A B C: Set U} (h₁: A ⊆ C) (h₂: B ⊆ C): A ∪ B ⊆ C := by
  intro x
  intro
    | .inl h => exact h₁ h
    | .inr h => exact h₂ h

/-
## Union of Subset Swap
-/

theorem union_sub_swap (A B: Set U): A ∪ B ⊆ B ∪ A
  | _, .inl h => .inr h
  | _, .inr h => .inl h

example {A B: Set U}: A ∪ B ⊆ B ∪ A := by
  intro x
  intro
    | .inl h => exact Or.inr h
    | .inr h => exact Or.inl h

/-
## Union is Commutative
-/

theorem union_comm (A B: Set U): A ∪ B = B ∪ A :=
  have h₁: A ∪ B ⊆ B ∪ A := union_sub_swap A B
  have h₂: B ∪ A ⊆ A ∪ B := union_sub_swap B A
  -- sub_antisymm h₁ h₂
  sorry

example (A B: Set U): A ∪ B = B ∪ A := by
  apply sub_antisymm
  · exact union_sub_swap A B
  · exact union_sub_swap B A

/-
## Union is Associative
-/

theorem union_assoc (A B C: Set U): (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
  have h₁: (A ∪ B) ∪ C ⊆ A ∪ (B ∪ C)
    | _, .inl (.inl h) => .inl h
    | _, .inl (.inr h) => .inr (.inl h)
    | _, .inr h        => .inr (.inr h)
  have h₂: A ∪ (B ∪ C) ⊆ (A ∪ B) ∪ C
    | _, .inl h        => .inl (.inl h)
    | _, .inr (.inl h) => .inl (.inr h)
    | _, .inr (.inr h) => .inr h
  -- sub_antisymm h₁ h₂
  sorry

example {A B C: Set U}: (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  apply sub_antisymm
  · intro x
    intro
      | .inl (.inl h) => exact Or.inl h
      | .inl (.inr h) => exact Or.inr (.inl h)
      | .inr h        => exact Or.inr (.inr h)
  · intro x
    intro
      | .inl h        => exact Or.inl (.inl h)
      | .inr (.inl h) => exact Or.inl (.inr h)
      | .inr (.inr h) => exact Or.inr h
