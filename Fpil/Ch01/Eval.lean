/-
# 1.1 Evaluating Expressions
-/

import Fpil.Abbrev

/- ## Examples -/

example: 1 + 2 = 3 := by rfl
example: 1 + 2 * 5 = 11 := by rfl

example: String.append "Hello, " "Lean!" = "Hello, Lean!" := by rfl
example: String.append "Great " (String.append "oak " "tree") = "Great oak tree" := by rfl

example: String.append "it is " (if 1 > 2 then "yes" else "no") = "it is no" := by rfl

/- ## Exercises -/

example: 42 + 19 = 61 := by rfl
example: String.append "A" (String.append "B" "C") = "ABC" := by rfl
example: String.append (String.append "A" "B") "C" = "ABC" := by rfl
example: (if 3 == 3 then 5 else 7) = 5 := by rfl
example: (if 3 == 4 then "equal" else "not equal") = "not equal" := by rfl
