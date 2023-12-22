theorem onePlusOneIsTwo: 1 + 1 = 2 := by
  simp

theorem addAndAppend: 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  simp

theorem andImpliesOr: A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
      | And.intro a _ => Or.inl a

theorem onePlusOneAndLessThan: 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualsFive: ¬(2 = 5) := by simp
theorem trueIsTrue: True := by simp
theorem trueOrFalse: True ∨ False := by simp
theorem falseImpliesTrue: False → True := by simp

def third (l: List α) (ok: l.length > 2): α := l[2]

def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

#eval third woodlandCritters (by simp)

theorem thm1: 2 + 3 = 5 := by simp
theorem thm2: 15 - 8 = 7 := by simp
theorem thm3: "Hello, ".append "world" = "Hello, world" := by simp
theorem thm4: 5 < 18 := by simp

def fifth (l: List α) (len: l.length > 4): α := l[4]
#eval fifth [1, 2, 3, 4, 5] (by simp)
