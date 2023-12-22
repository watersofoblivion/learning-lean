/-
# Structures and Records
-/

/-
## Declaring Structures
-/

structure Point (α: Type u) where
  x: α
  y: α
deriving Repr

#check Point
#check @Point.rec
#check Point.mk
#check Point.x
#check Point.y

#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

example (a b: α): Point.x (Point.mk a b) = a := rfl
example (a b: α): Point.y (Point.mk a b) = b := rfl

def p := Point.mk 10 20

#check p.x
#eval p.x
#eval p.y

def Point.add (p q: Point Nat) :=
  Point.mk (p.x + q.x) (p.y + q.y)

def q: Point Nat := Point.mk 3 4

#eval p.add q

def Point.smul (n: Nat) (p: Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

#eval p.smul 3

#check @List.map

def l := [1, 2, 3]
def f: Nat -> Nat
  | n => n * n

#eval l.map f

/-
## Objects
-/

#check { x := 10, y := 20: Point Nat }
#check { y := 20, x := 10: Point _ }
#check ({ x := 10, y := 20 }: Point Nat)

example: Point Nat := { y := 20, x := 10 }

structure MyStruct where
  {α: Type u}
  {β: Type v}
  a: α
  b: β

#check { a := 10, b := true: MyStruct }

#eval { p with x := 3 }
#eval { p with y := 4 }

structure Point3D (α: Type u) where
  x: α
  y: α
  z: α

def r: Point3D Nat := { x := 5, y := 5, z := 5 }
def s: Point3D Nat := { p, r with x := 6 }

example: s.x = 6 := rfl
example: s.y = 20 := rfl
example: s.z = 5 := rfl

/-
## Inheritance
-/

inductive Color where
  | red
  | green
  | blue

structure ColoredPoint (α: Type u) extends Point α where
  c: Color

structure RGBValue where
  red: Nat
  green: Nat
  blue: Nat

structure RedGreenPoint (α: Type) extends Point α, RGBValue where
  no_blue: blue = 0

def rgp: RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example: rgp.x = 10 := rfl
example: rgp.red = 200 := rfl
