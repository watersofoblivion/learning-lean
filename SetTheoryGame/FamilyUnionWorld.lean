/-
# Family Union World
-/

import «SetTheoryGame».«SubsetWorld»
import «SetTheoryGame».«ComplementWorld»
import «SetTheoryGame».«IntersectionWorld»
import «SetTheoryGame».«UnionWorld»
import «SetTheoryGame».«FamilyIntersectionWorld»

/-
## Proving Existential Statements
-/

example (A: Set U) : ∃ S, S ⊆ A :=
  ⟨A, sub_refl A⟩

example (A: Set U) : ∃ S, S ⊆ A := by
  apply Exists.intro
  · apply sub_refl

/-
## Subset of Family Union
-/

-- example {A: Set U} {F: Set (Set U)} (h₁: A ∈ F) : A ⊆ ⋃₀ F := by sorry
