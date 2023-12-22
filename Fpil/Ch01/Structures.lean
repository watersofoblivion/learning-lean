/-
# 1.4 Structures
-/

import Fpil.Abbrev

#check 1.2
#check -454.2123215
#check 0.0

#check 0
#check (0: Float)
#check (0: ℝ)

/-- 2-Dimensional Points -/
structure Point where
  x: ℝ
  y: ℝ
deriving Repr

def origin: Point := ⟨0, 0⟩

example: origin = ⟨0, 0⟩ := by rfl
example: origin.x = 0 := by rfl
example: origin.y = 0 := by rfl

def Point.add (p₁ p₂: Point): Point := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩
def Point.distance (p₁ p₂: Point): ℝ :=
  let diffX := p₂.x - p₁.x
  let diffY := p₂.y - p₁.y
  Float.sqrt ((diffX ^ 2.0) + (diffY ^ 2.0))

#eval (origin.add ⟨1.5, 32⟩).add ⟨-8, 0.2⟩
#eval (⟨1, 2⟩: Point).distance ⟨5, -1⟩

/-- 3-Dimensional Points -/
structure Point3D where
  x: ℝ
  y: ℝ
  z: ℝ
deriving Repr

def origin3d: Point3D := ⟨0, 0, 0⟩

/-
## Updating Structures
-/
