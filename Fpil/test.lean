#eval 1 + 2
#eval 1 + 2 * 5
#eval String.append "Hello, " "World!"
#eval String.append "great " (String.append "oak " "tree")
#eval String.append "it is " (if 1 > 2 then "yes" else "no")
-- #eval String.append "it is "

def hello := "Hello"
def lean: String := "Lean"
#eval String.append hello (String.append " " lean)

def add1 (n: Nat) := n + 1
#eval add1 7

def maximum (x: Nat) (y: Nat) := if x > y then x else y
#eval maximum (5 + 8) (2 * 7)

#check add1
#check maximum

def joinStringsWith (combiner left right: String) :=
  String.append left (String.append combiner right)
#eval joinStringsWith ", " "one" "and another"
#check joinStringsWith ", "

def volume (height width depth: Nat) := height * width * depth

#check 1.2
#check -454.2123215
#check 0.0

#check 0
#check (0: Float)

structure Point where
  point::
  x: Float
  y: Float
deriving Repr

def origin: Point := { x := 0.0, y := 0.0 }
#eval origin
#eval origin.x
#eval origin.y

def addPoints (p1 p2: Point): Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
def distance (p1 p2: Point): Float :=
  let diffX := p2.x - p1.x
  let diffY := p2.y - p1.y
  Float.sqrt (diffX ^ 2.0) + (diffY ^ 2.0)
#eval distance { x := 1, y:= 2 } { x := 5, y := -1 }

structure Point3D where
  x: Float
  y: Float
  z: Float
deriving Repr

def origin3D: Point3D := { x := 0.0, y := 0.0, z := 0.0 }

#check { x := 0, y := 0 : Point}
def zeroX (p: Point): Point :=
  { p with x := 0 }
def fourAndThree: Point := { x := 4.3, y := 3.4 }
#eval fourAndThree
#eval zeroX fourAndThree
#eval fourAndThree

#check Point.point 1.5 2.8
#check Point.point
#check Point.x
#check Point.y

#eval origin.x
#eval Point.x origin

#eval "one string".append " and another"

def Point.modifyBoth (f: Float → Float) (p: Point): Point :=
  { x := f p.x, y := f p.y: Point }
#eval fourAndThree.modifyBoth Float.floor

structure RectangularPrism where
  width: Float
  height: Float
  depth: Float
deriving Repr

def RectangularPrism.volume (p: RectangularPrism): Float :=
  p.width * p.depth * p.height
def testPrism: RectangularPrism := { width := 2, height := 3, depth := 5 }
#eval testPrism.volume

structure Segment where
  a: Point3D
  b: Point3D
deriving Repr

def Segment.length (seg: Segment): Float :=
  let diffX := seg.a.x - seg.b.x
  let diffY := seg.a.y - seg.b.y
  let diffZ := seg.a.z - seg.b.z
  Float.sqrt (diffX ^ 2) + (diffY ^ 2) + (diffZ ^ 2)

def isZero (n: Nat): Bool :=
  match n with
    | Nat.zero =>  true
    | Nat.succ _ => false

#eval isZero Nat.zero
#eval isZero 42

def pred (n: Nat): Nat :=
  match n with
    | Nat.zero => 0
    | Nat.succ n' => n'

def Point3D.depth (p: Point3D): Float :=
  match p with
    | { x := _, y := _, z := d } => d

def isEven (n: Nat): Bool :=
  match n with
    | Nat.zero => true
    | Nat.succ k => not (isEven k)
#eval isEven 42
#eval isEven 99

def add (x y: Nat): Nat :=
  match x with
    | Nat.zero => y
    | Nat.succ x' => add x' (Nat.succ y)

#eval add 42 10

def times (x y: Nat): Nat :=
  match y with
    | Nat.zero => x
    | Nat.succ y' => add x (times x y')

def minus (x y: Nat): Nat :=
  match y with
    | Nat.zero => 0
    | Nat.succ y' => pred (minus x y')

structure PPoint (α: Type) where
  x: α
  y: α
deriving Repr

def natOrigin: PPoint Nat := { x := 0, y := 0 }
def replaceX {α: Type} (point: PPoint α) (x: α): PPoint α :=
  { point with x := x }

#check replaceX
#check replaceX
#check replaceX natOrigin
#check replaceX natOrigin 5

#eval replaceX natOrigin 5

inductive Sign where
  | pos
  | neg

def posOrNegThree (s: Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
    | Sign.pos => 3
    | Sign.neg => -3

def primesUnder10: List Nat := [2, 3, 5, 7]

def length {α: Type} (l: List α): Nat :=
  match l with
    | [] => 0
    | _::tl => 1 + length tl

#eval length primesUnder10
#eval primesUnder10.length

#check List.length
#eval primesUnder10.head?
#eval [].head? (α := Nat)

def fives: String × Int := ("five", 5)
def sevens: String × Int × Nat := ("seven", 7, 4 + 3)

def PetName: Type := String ⊕ String
def animals: List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (names: List PetName): Nat :=
  match names with
    | [] => 0
    | Sum.inl _ :: names => 1 + howManyDogs names
    | Sum.inr _ :: names => howManyDogs names

#eval howManyDogs animals

def last {α: Type} (l: List α): Option α :=
  match l with
    | [] => none
    | hd::[] => some hd
    | _::tl => last tl

def List.findFirst? {α: Type} (l: List α) (p: α -> Bool): Option α :=
  match l with
    | [] => none
    | hd::tl => if p hd then hd else tl.findFirst? p

def swap (α β: Type) (p: α × β): β × α :=
  (p.snd, p.fst)

inductive Animal: Type where
  | dog : String → Animal
  | cat : String → Animal

def inductivePetNames: List Animal := [Animal.dog "Spot", Animal.cat "Tiger", Animal.dog "Fifi", Animal.dog "Rex", Animal.cat "Floof"]
def inductiveHowManyDogs (pets: List Animal): Nat :=
  match pets with
    | [] => 0
    | Animal.dog _ :: pets => 1 + inductiveHowManyDogs pets
    | Animal.cat _ :: pets => inductiveHowManyDogs pets

def zip {α β: Type} (a: List α) (b: List β): List (α × β) :=
  match a, b with
    | [], [] => []
    | [], _ => []
    | _, [] => []
    | hd::tl, hd'::tl' => (hd, hd') :: zip tl tl'

def take {α: Type} (n: Nat) (l: List α): List α :=
  match n, l with
    | _, [] => []
    | Nat.zero, _ => []
    | Nat.succ n', hd :: tl => hd :: take n' tl

#eval take 3 ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"]

-- def dist {α β γ: Type} (x: α × (β ⊕ γ)): (a × β) ⊕ (α × γ) :=
--   match x.snd with
--     | Sum.inl b => Sum.inl (x.fst, b)
--     | Sum.inr g => Sum.inr (x.fst, g)

def timesBool {α: Type} (x: Bool × α): α ⊕ α :=
  if x.fst then Sum.inl x.snd else Sum.inr x.snd

#eval (⟨1, 2⟩: PPoint Float)
