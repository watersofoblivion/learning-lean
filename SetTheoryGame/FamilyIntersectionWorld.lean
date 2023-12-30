/-
# Family Intersection World
-/

import «SetTheoryGame».«SubsetWorld»
import «SetTheoryGame».«ComplementWorld»
import «SetTheoryGame».«IntersectionWorld»
import «SetTheoryGame».«UnionWorld»

-- theorem fam_inter_def {U: Type} (x: U) (F: Set U → Set (Set U)) : x ∈ ⋂ F ↔ ∀ S ∈ F, x ∈ S := sorry

/-
## Family Intersection is Subset
-/

-- example {A: Set U} {F: Set (Set U)} (h₁: A ∈ F): ⋂₀ F ⊆ A := by
--   sorry
