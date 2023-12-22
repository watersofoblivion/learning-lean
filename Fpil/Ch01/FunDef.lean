/-
# 1.3 Functions and Definitions
-/

import Fpil.Abbrev

/- ## Defining Functions -/

def hello := "Hello"
def lean: String := "Lean"

example: String.append hello (String.append " " lean) = "Hello Lean" := by rfl

def add1 (n: ℕ): ℕ := n + 1
example: add1 7 = 8 := by rfl

def maximum (n k: ℕ): ℕ :=
  if n > k then n else k
example: maximum (5 + 8) (2 * 7) = 14 := by rfl

#check add1
#check maximum

#check (add1)
#check (maximum)

/- ### Exercises -/

def joinStringsWith (comb sₗ sᵣ: String): String :=
  String.append (String.append sₗ comb) sᵣ
#check (joinStringsWith)

example: joinStringsWith ", " "one" "and another" = "one, and another" := by rfl

def volume (h w d: ℕ): ℕ := h * w * d

/- ## Defining Types -/

def Str: Type := String
def aStr: Str := "This is a string"

/- ### Exercises -/
