import Lean

class Plus (α: Type) where
  plus: α → α → α

open Plus (plus)


instance: Plus Nat where
  plus := Nat.add

#eval Plus.plus 3 5
#eval plus 3 5


inductive Pos: Type where
  | one: Pos
  | succ: Pos → Pos

def Pos.plus: Pos → Pos → Pos
    | Pos.one, y => Pos.succ y
    | Pos.succ x', y => Pos.succ (x'.plus y)

instance: Plus Pos where
  plus := Pos.plus

instance: Add Pos where
  add := Pos.plus

def Pos.mul: Pos → Pos → Pos
    | Pos.one, y => y
    | Pos.succ x', y => x'.mul y + y

instance: Mul Pos where
  mul := Pos.mul

def Pos.toString (paren: Bool) (p: Pos): String :=
  let parenthesize s := if paren then "(" ++ s ++ ")" else s
  match p with
    | Pos.one => "Pos.one"
    | Pos.succ p' => parenthesize (s!"Pos.succ {Pos.toString true p'}")

def Pos.toNat (p: Pos): Nat :=
  match p with
    | Pos.one => 1
    | Pos.succ p' => 1 + p'.toNat

instance: ToString Pos where
  toString := Pos.toString false

instance: ToString Pos where
  toString x := toString x.toNat

instance: OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne: Nat → Pos
      | 0 => Pos.one
      | n + 1 => Pos.succ (natPlusOne n)
    natPlusOne n

def seven: Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
#eval seven

def fourteen: Pos := plus seven seven
def fourteen': Pos := seven + seven
#eval fourteen
#eval fourteen'

def fourtyNine: Pos := seven * seven
#eval fourtyNine

#eval (8: Pos)

structure NPos where
  succ ::
  pred: Nat

instance: Add NPos where
  add x y := NPos.succ (1 + x.pred + y.pred)

instance: ToString NPos where
  toString p := toString (p.pred + 1)

instance: OfNat NPos (n + 1) where
  ofNat := NPos.succ n

#eval (42: NPos)
#eval toString ((4: NPos) + (2: NPos))
#eval toString ((17: NPos) + (32: NPos))

inductive Even where
  | zero: Even
  | plusTwo: Even → Even

def Even.add: Even → Even → Even
    | Even.zero, y => y
    | Even.plusTwo x, y => Even.plusTwo (x.add y)

def Even.toNat: Even -> Nat
  | Even.zero => 0
  | Even.plusTwo n => 2 + n.toNat

instance: Add Even where
  add := Even.add

instance: ToString Even where
  toString n := toString n.toNat

def zero: Even := Even.zero
def two: Even := Even.plusTwo Even.zero
def four: Even := Even.plusTwo two
def six: Even := Even.plusTwo four
def eight: Even := Even.plusTwo six

#eval [zero, two, four, six, eight]

inductive HttpVersion where
  | one
  | oneOne
  | two

inductive HttpMethod where
  | options
  | get
  | post
  | put
  | delete

structure HttpRequest where
  method: HttpMethod
  uri: String
  version: HttpVersion

structure HttpResponse where
  status: Nat
  headers: List (String × List String)
  body: String



#check @IO.println

def List.sum [Add α] [OfNat α 0]: List α → α
  | [] => 0
  | hd::tl => hd + tl.sum

def fourNats: List Nat := [1, 2, 3, 4]
#eval fourNats.sum

def fourPos: List Pos := [1, 2, 3, 4]
-- #eval fourPos.sum

#check OfNat.ofNat

instance: OfNat Even Nat.zero where
  ofNat := Even.zero

-- instance: OfNat Even (Nat.succ (Nat.succ n)) where
--   ofNat := Even.plusTwo (Even.ofNat n)

def addNatPos: Nat → Pos → Pos
  | Nat.zero, p => p
  | Nat.succ n, p => 1 + (addNatPos n p)
def addPosNat: Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => 1 + (addPosNat p n)

instance: HAdd Nat Pos Pos where
  hAdd := addNatPos
instance: HAdd Pos Nat Pos where
  hAdd := addPosNat

def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]
#eval northernTrees.size

structure NonEmptyList (α: Type): Type where
  head: α
  tail: List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get?: NonEmptyList α → Nat → Option α
  | lst, 0 => some lst.head
  | { head := _, tail := [] }, _ => none
  | { head := _, tail := hd :: tl }, n + 1 => get? { head := hd, tail := tl } n

abbrev NonEmptyList.inBounds (l: NonEmptyList α) (n: Nat): Prop :=
  n ≤ l.tail.length

theorem atLeastThreeSpiders: idahoSpiders.inBounds 2 := by simp
theorem notSixSpiders: ¬idahoSpiders.inBounds 6 := by simp

def NonEmptyList.get (l: NonEmptyList α) (n: Nat) (inBounds: l.inBounds n): α :=
  match n with
    | 0 => l.head
    | n + 1 => l.tail[n]

instance: GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

instance: GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (lst: List α) (n: Pos) ok := lst[n.toNat]

theorem FnEq: (fun (x: Nat) => x + 1) = (Nat.succ ·) := by
  simp

#check 2 < 4

def Pos.compare: Pos -> Pos -> Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, _ => Ordering.lt
  | _, Pos.one => Ordering.gt
  | Pos.succ p, Pos.succ p' => compare p p'

instance: Ord Pos where
  compare := Pos.compare

def Pos.hash: Pos -> UInt64
  | Pos.one => 0
  | Pos.succ p => mixHash 1 (p.hash)

instance: Hashable Pos where
  hash := Pos.hash

instance [Hashable α]: Hashable (NonEmptyList α) where
  hash lst := mixHash (hash lst.head) (hash lst.tail)

inductive BinTree (α: Type) :=
  | leaf: BinTree α
  | node: BinTree α → α → BinTree α → BinTree α

def BinTree.beq [BEq α]: BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf => true
  | BinTree.node t₁ₗ x₁ t₁ᵣ, BinTree.node t₂ₗ x₂ t₂ᵣ =>
    x₁ == x₂ &&  beq t₁ₗ t₂ₗ && beq t₁ᵣ t₂ᵣ
  | _, _ => false

instance [BEq α]: BEq (BinTree α) where
  beq := BinTree.beq

def BinTree.hash [Hashable α]: BinTree α → UInt64
  | BinTree.leaf => 0
  | BinTree.node tₗ x tᵣ =>
    mixHash 1 (mixHash (hash tₗ) (mixHash (Hashable.hash x) (hash tᵣ)))

instance [Hashable α]: Hashable (BinTree α) where
  hash := BinTree.hash

deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable, Repr for NonEmptyList

instance: Append (NonEmptyList α) where
  append lst₁ lst₂ :=
    { head := lst₁.head, tail := lst₁.tail ++ lst₂.head :: lst₂.tail }

#eval idahoSpiders ++ idahoSpiders

instance: HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend l₁ l₂ :=
    { head := l₁.head, tail := l₁.tail ++ l₂ }

#eval idahoSpiders ++ ["Trapdoor Spider"]

instance: Functor NonEmptyList where
  map f l := { head := f l.head, tail := f <$> l.tail }

instance: HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend: List α → NonEmptyList α → NonEmptyList α
    | [], l => l
    | hd :: tl, l => { head := hd, tail := tl ++ l.tail }


#eval ([]: List String) ++ idahoSpiders
#eval ["foo", "bar", "baz"] ++ idahoSpiders

def BinTree.map (f: α → β) (t: BinTree α): BinTree β :=
  match t with
    | BinTree.leaf => BinTree.leaf
    | BinTree.node tₗ x tᵣ => BinTree.node (map f tₗ) (f x) (map f tᵣ)

instance: Functor BinTree where
  map := BinTree.map

instance: Coe Pos Nat where
  coe := Pos.toNat

#eval [1, 2, 3, 4].drop (2: Pos)
#eval [1, 2, 3, 4].drop (10: Pos)
#check [1, 2, 3, 4].drop (2: Pos)

def oneInt: Int := Pos.one
#check (Pos.one: Int)

inductive A where | a deriving Repr
inductive B where | b deriving Repr

instance: Coe A B where
  coe _ := B.b
instance: Coe B A where
  coe _ := A.a
instance: Coe Unit A where
  coe _ := A.a

def coerceToB: B := ()
#eval coerceToB

def List.last?: List α → Option α
  | [] => none
  | hd :: [] => hd
  | _ :: tl => last? tl

def perhapsPerhapsPerhaps: Option (Option (Option String)) := "Please don't tell me"
def perhapsPerhapsPerhapsNot: Option (Option (Option Nat)) := ↑(42: Nat)

instance: Coe (NonEmptyList α) (List α) where
  coe l := l.head :: l.tail

instance: CoeDep (List α) (hd :: tl) (NonEmptyList α) where
  coe := { head := hd, tail := tl }

structure Monoid where
  Carrier: Type
  neutral: Carrier
  op: Carrier → Carrier → Carrier

def natMulMonoid: Monoid := { Carrier := Nat, neutral := 1, op := (· * ·) }
def natAddMonoid: Monoid := { Carrier := Nat, neutral := 0, op := (· + ·) }
def stringMoniod: Monoid := { Carrier := String, neutral := "", op := (· ++ ·) }
def listMonoid (α: Type): Monoid := { Carrier := List α, neutral := [], op := (· ++ ·) }

instance: CoeSort Monoid Type where
  coe m := m.Carrier

def foldMap (M: Monoid) (f: α → M) (l: List α): M :=
  let rec foldMap' (acc: M): List α -> M
    | [] => acc
    | hd :: tl => foldMap' (M.op acc (f hd)) tl
  foldMap' M.neutral l

instance: CoeSort Bool Prop where
  coe b := b = true

structure Adder where
  amt: Nat

def add5: Adder := ⟨5⟩

instance: CoeFun Adder (fun _ => Nat → Nat) where
  coe adder := (· + adder.amt)

#eval add5 10

inductive JSON where
  | true: JSON
  | false: JSON
  | null: JSON
  | string: String → JSON
  | number: Float → JSON
  | array: List JSON → JSON
  | object: List (String × JSON) → JSON
deriving Repr

structure Serializer where
  Contents: Type
  serialize: Contents → JSON

def Str: Serializer :=
  { Contents := String, serialize := JSON.string }

instance: CoeFun Serializer (fun ser => ser.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title: String) (R: Serializer) (record: R.Contents): JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

#eval buildResponse "Functional programming in Lean" Str "Dependent Types r fun!"

def String.dropDecimal (s: String): String :=
  if s.contains '.'
  then (s.dropRightWhile (· == '0')).dropRightWhile (· == '.')
  else s

def String.separate (sep: String) (strs: List String): String :=
  match strs with
    | [] => ""
    | hd :: tl => String.join (hd :: (tl.map (sep ++ .)))

#eval ", ".separate ["foo", "bar", "baz"]
#eval ", ".separate ["foo"]
#eval ", ".separate []

partial def JSON.toString (val: JSON): String :=
  match val with
    | true => "true"
    | false => "false"
    | null => "null"
    | string s => "\"" ++ Lean.Json.escape s ++ "\""
    | number n => n.toString.dropDecimal
    | object elems =>
      let elemStr elem := "\"" ++ Lean.Json.escape elem.fst ++ "\": " ++ toString elem.snd
      "{" ++ ", ".separate (elems.map elemStr) ++ "}"
    | array elems =>
      "[" ++ ", ".separate (elems.map toString) ++ "]"

instance: ToString JSON where
  toString := JSON.toString

#eval (buildResponse "Functional programming in Lean" Str "Dependent Types r fun!").toString
