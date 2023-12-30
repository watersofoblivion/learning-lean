/-
# Intersection World
-/

import «SetTheoryGame».«SubsetWorld»
import «SetTheoryGame».«ComplementWorld»

/-
## And
-/

example {x: U} (A B: Set U): x ∈ A ∧ x ∈ B → x ∈ A
  | ⟨h, _⟩ => h

example {x: U} (A B: Set U) (h: x ∈ A ∧ x ∈ B): x ∈ A := by
  exact h.left

/-
## Element of an Intersection
-/

example {x: U} {A B: Set U}: x ∈ A ∩ B → x ∈ B
  | ⟨_, hb⟩ => hb

example {x: U} {A B: Set U} (h: x ∈ A ∩ B): x ∈ B := by
  exact h.right

/-
## Intersection is a Subset
-/

example {A B: Set U}: A ∩ B ⊆ A
  | _, h => h.left

example {A B: Set U}: A ∩ B ⊆ A := by
  intro x h
  exact h.left

/-
## Proving a Conjunction
-/

example {x: U} {A B: Set U}: x ∈ A → x ∈ B → x ∈ A ∩ B
  | hxa, hxb => ⟨hxa, hxb⟩

example {x: U} {A B: Set U} (h₁: x ∈ A) (h₂: x ∈ B): x ∈ A ∩ B := by
  apply And.intro h₁ h₂

/-
## Subset of an Intersection
-/

example {A B C: Set U}: A ⊆ B → A ⊆ C → A ⊆ B ∩ C
  | hab, hac, _, y => ⟨hab y, hac y⟩

example {A B C: Set U} (h₁: A ⊆ B) (h₂: A ⊆ C): A ⊆ B ∩ C := by
  intro x h₃
  apply And.intro
  · exact h₁ h₃
  · exact h₂ h₃

/-
## Intersection Subset of Swap
-/

theorem inter_sub_swap (A B: Set U): A ∩ B ⊆ B ∩ A
  | _, ⟨ha, hb⟩ => ⟨hb, ha⟩

example {A B: Set U}: A ∩ B ⊆ B ∩ A := by
  intro x h
  apply And.intro h.right h.left

/-
## Intersection is Commutative
-/

theorem inter_comm {U: Type} (A B: Set U): A ∩ B = B ∩ A :=
  have h₁: A ∩ B ⊆ B ∩ A := inter_sub_swap A B
  have h₂: B ∩ A ⊆ A ∩ B := inter_sub_swap B A
  sub_antisymm h₁ h₂

example {A B: Set U}: A ∩ B = B ∩ A := by
  apply sub_antisymm
  . exact inter_sub_swap A B
  . exact inter_sub_swap B A

/-
## Intersection is Associative
-/

theorem inter_assoc {U: Type} (A B C: Set U): (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
  have h₁: (A ∩ B) ∩ C ⊆ A ∩ (B ∩ C)
    | _, ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, ⟨hb, hc⟩⟩
  have h₂: A ∩ (B ∩ C) ⊆ (A ∩ B) ∩ C
    | _, ⟨ha, ⟨hb, hc⟩⟩ => ⟨⟨ha, hb⟩, hc⟩
  sub_antisymm h₁ h₂

example {A B C: Set U}: (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  apply sub_antisymm
  . intro x h
    apply And.intro
    · exact h.left.left
    · apply And.intro h.left.right h.right
  . intro x h
    apply And.intro
    · exact And.intro h.left h.right.left
    · exact h.right.right
