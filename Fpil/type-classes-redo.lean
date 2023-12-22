/-
# 4.1 Positive Numbers
-/

-- Example Addition Typeclass -
class Plus (α: Type) where
  plus: α → α → α

instance: Plus Nat where
  plus := Nat.add

#eval Plus.plus 3 5

/--
# Positive numbers

Similar to natural numbers, but excludes zero (`0`).  The standard running
example for section 4.1 of
[Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/type-classes/pos.html).
-/
inductive ℙ: Type where
  | one: ℙ
  | succ: ℙ → ℙ
deriving BEq, Ord, Hashable

def ℙ.add: ℙ → ℙ → ℙ
  | .one, k => ℙ.succ k
  | .succ p, k => .succ (p.add k)

def ℙ.mul: ℙ → ℙ → ℙ
  | .one, k => k
  | .succ p, k => (p.mul k).add k

def ℙ.toNat: ℙ → Nat
  | .one => 1
  | .succ p => 1 + p.toNat

def ℙ.natAdd: Nat → ℙ → ℙ
    | 0, p => p
    | n + 1, p => ℙ.succ (natAdd n p)

def ℙ.addNat (p: ℙ) (n: Nat): ℙ := ℙ.natAdd n p

def ℙ.beq: ℙ → ℙ → Bool
  | .one, one => true
  | .succ p₁, .succ p₂ => beq p₁ p₂
  | _, _ => false

def ℙ.compare: ℙ → ℙ → Ordering
  | .one, .one => Ordering.eq
  | .one, _ => Ordering.lt
  | _, .one => Ordering.gt
  | .succ p₁, .succ p₂ => compare p₁ p₂

def ℙ.hash: ℙ -> UInt64
  | .one => 0
  | .succ p => mixHash 1 (hash p)

instance: Plus ℙ where
  plus := ℙ.add

-- Stdlib Typeclass Implementations

instance: Add ℙ where add := ℙ.add
instance: HAdd Nat ℙ ℙ where hAdd := ℙ.natAdd
instance: HAdd ℙ Nat ℙ where hAdd := ℙ.addNat
instance: Mul ℙ where mul := ℙ.mul
instance: ToString ℙ where toString x := toString x.toNat
instance: OfNat ℙ (n + 1) where
  ofNat :=
    let rec natPlusOne: Nat -> ℙ
      | .zero => ℙ.one
      | .succ n => ℙ.succ (natPlusOne n)
    natPlusOne n
instance: Coe ℙ Nat where coe := ℙ.toNat

-- Examples

def sevenₚ: ℙ := 7
def fourteenₚ: ℙ := sevenₚ + sevenₚ
def fourtyNine: ℙ := sevenₚ * sevenₚ

example: ℙ := 7
example: ℙ := 14
example: List ℙ := [sevenₚ * 1, sevenₚ * sevenₚ, 2 * sevenₚ]

/--
# Successor Positives

Another representation of positive numbers, this time as the successor to a
natural number.
-/
structure ℙₙ: Type where
  n: Nat
deriving BEq, Ord, Hashable

def ℙₙ.add (x y: ℙₙ): ℙₙ := ⟨1 + x.n + y.n⟩
def ℙₙ.mul (x y: ℙₙ): ℙₙ := ⟨x.n * y.n + x.n + y.n⟩
def ℙₙ.toNat (p: ℙₙ): Nat := p.n + 1
def ℙₙ.natAdd: Nat → ℙₙ → ℙₙ
  | 0, p => p
  | n + 1, p => ⟨p.n + n⟩
def ℙₙ.addNat (p: ℙₙ) (n: Nat): ℙₙ := ℙₙ.natAdd n p

-- Stdlib Typeclass Implementations

instance: Add ℙₙ where add := ℙₙ.add
instance: HAdd Nat ℙₙ ℙₙ where hAdd := ℙₙ.natAdd
instance: HAdd ℙₙ Nat ℙₙ where hAdd := ℙₙ.addNat
instance: Mul ℙₙ where mul := ℙₙ.mul
instance: ToString ℙₙ where toString p := toString p.toNat
instance: OfNat ℙₙ (n + 1) where ofNat := ⟨n⟩
instance: Coe ℙₙ Nat where coe := ℙₙ.toNat

-- Examples
def sevenₙ: ℙₙ := 7
def fourteenₙ: ℙₙ := sevenₙ + sevenₙ

example: ℙₙ := 7
example: ℙₙ := 14
example: List ℙₙ := [sevenₙ * 1, sevenₙ * sevenₙ, 2 * sevenₙ]

/-
# Even and Odd Numbers

Even and odd numbers, represented as `2k` and `2k + 1`, respectively.
-/


structure 𝔼: Type where n: Nat deriving BEq, Ord, Hashable
structure 𝕆: Type where n: Nat deriving BEq, Ord, Hashable

@[simp]
private def add (n₁ n₂: Nat) := (2 * n₁ + 2 * n₂) / 2
@[simp]
private def mul (n₁ n₂: Nat) := 2 * n₁ * n₂

@[simp]
def 𝔼.addEven (e₁ e₂: 𝔼): 𝔼 := ⟨add e₁.n e₂.n⟩
@[simp]
def 𝔼.addOdd (e: 𝔼) (o: 𝕆): 𝕆 := ⟨add e.n o.n⟩
@[simp]
def 𝔼.mulEven (e₁ e₂: 𝔼): 𝔼 := ⟨mul e₁.n e₂.n⟩
@[simp]
def 𝔼.mulOdd (e: 𝔼) (o: 𝕆): 𝔼 := ⟨mul e.n o.n + e.n⟩

@[simp]
def 𝕆.addEven (o: 𝕆) (e: 𝔼): 𝕆 := ⟨add o.n e.n⟩
@[simp]
def 𝕆.addOdd (o₁ o₂: 𝕆): 𝔼 := ⟨add o₁.n o₂.n + 1⟩
@[simp]
def 𝕆.mulEven (o: 𝕆) (e: 𝔼): 𝔼 := ⟨mul e.n o.n + e.n⟩
@[simp]
def 𝕆.mulOdd (o₁ o₂: 𝕆): 𝕆 := ⟨mul o₁.n o₂.n + o₁.n + o₂.n⟩

@[simp]
def 𝔼.toNat (e: 𝔼): Nat := 2 * e.n
@[simp]
def 𝕆.toNat (o: 𝕆): Nat := 2 * o.n + 1

-- Proofs

theorem 𝔼.toNatSound:
  ∀ n: Nat,
  (⟨n⟩: 𝔼).toNat = 2 * n := by
    intro n
    simp

theorem 𝕆.toNatSound:
  ∀ n: Nat,
  (⟨n⟩: 𝕆).toNat = 2 * n + 1 := by
    intro n
    simp

-- theorem 𝔼.addEvenSound:
--   ∀ n₁ n₂: Nat,
--   ((⟨n₁⟩: 𝔼).addEven ⟨n₂⟩).toNat = 2 * n₁ + 2 * n₂ := by
--     intro n₁ n₂
--     simp

-- theorem 𝔼.addOddSound:
--   ∀ n₁ n₂: Nat,
--   ((⟨n₁⟩: 𝔼).addOdd ⟨n₂⟩).toNat = 2 * n₁ + (2 * n₂ + 1) := by
--     intro n₁ n₂
--     simp

-- theorem 𝔼.mulEvenSound:
--   ∀ n₁ n₂: Nat,
--   ((⟨n₁⟩: 𝔼).mulEven ⟨n₂⟩).toNat = 2 * n₁ * 2 * n₂ := by
--     intro n₁ n₂
--     simp

-- theorem 𝔼.mulOddSound:
--   ∀ n₁ n₂: Nat,
--   ((⟨n₁⟩: 𝔼).mulOdd ⟨n₂⟩).toNat = 2 * n₁ * (2 * n₂ + 1) := by
--     intro n₁ n₂
--     simp

-- theorem 𝕆.addEvenSound:
--   ∀ n₁ n₂: Nat,
--   ((⟨n₁⟩: 𝕆).addEven ⟨n₂⟩).toNat = (2 * n₁ + 1) + 2 * n₂ := by
--     intro n₁ n₂
--     simp

-- theorem 𝕆.addOddSound:
--   ∀ n₁ n₂: Nat,
--   ((⟨n₁⟩: 𝕆).addOdd ⟨n₂⟩).toNat = (2 * n₁ + 1) + (2 * n₂ + 1) := by
--     intro n₁ n₂
--     simp

-- theorem 𝕆.mulEvenSound:
--   ∀ n₁ n₂: Nat,
--   ((⟨n₁⟩: 𝕆).mulEven ⟨n₂⟩).toNat = (2 * n₁ + 1) * 2 * n₂ := by
--     intro n₁ n₂
--     simp

-- theorem 𝕆.mulOddSound:
--   ∀ n₁ n₂: Nat,
--   ((⟨n₁⟩: 𝕆).mulOdd ⟨n₂⟩).toNat = (2 * n₁ + 1) * (2 * n₂ + 1) := by
--     intro n₁ n₂
--     simp

-- Stdlib Typeclass Implementations

instance: HAdd 𝔼 𝔼 𝔼 where hAdd := 𝔼.addEven
instance: HAdd 𝔼 𝕆 𝕆 where hAdd := 𝔼.addOdd
instance: HAdd 𝕆 𝔼 𝕆 where hAdd := 𝕆.addEven
instance: HAdd 𝕆 𝕆 𝔼 where hAdd := 𝕆.addOdd

instance: HMul 𝔼 𝔼 𝔼 where hMul := 𝔼.mulEven
instance: HMul 𝔼 𝕆 𝔼 where hMul := 𝔼.mulOdd
instance: HMul 𝕆 𝔼 𝔼 where hMul := 𝕆.mulEven
instance: HMul 𝕆 𝕆 𝕆 where hMul := 𝕆.mulOdd

instance: ToString 𝔼 where toString e := toString e.toNat
instance: ToString 𝕆 where toString o := toString o.toNat

instance: OfNat 𝔼 0 where
  ofNat := ⟨0⟩
instance [OfNat 𝔼 n]: OfNat 𝔼 (n + 2) where
  ofNat := ⟨1 + (OfNat.ofNat (n / 2))⟩

instance: OfNat 𝕆 1 where
  ofNat := ⟨0⟩
instance [OfNat 𝕆 n]: OfNat 𝕆 (n + 2) where
  ofNat := ⟨1 + (OfNat.ofNat ((n - 1) / 2))⟩

instance: Coe 𝔼 Nat where coe := 𝔼.toNat
instance: Coe 𝕆 Nat where coe := 𝕆.toNat

/-
# 4.2 Type Classes and Polymorphism
-/

-- Sum a list of values
def List.sum [Add α] [OfNat α 0]: List α → α
  | [] => 0
  | hd :: tl => hd + sum tl

-- Exmaples
def fourNats: List Nat := [1, 2, 3, 4]
example: Nat := fourNats.sum

/--
# Polymorphic 2-Dimensional Points
-/
structure PPoint (α : Type): Type where
  x: α
  y: α
deriving Repr, BEq, Hashable

instance [Add α]: Add (PPoint α) where
  add p₁ p₂ := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

/-
# 4.3 Controlling Instance Search
-/

instance [Mul α]: HMul (PPoint α) α (PPoint α) where
  hMul (p: PPoint α) s :=
    ⟨p.x * s, p.y * s⟩

#eval (⟨2.5, 3.7⟩: PPoint Float) * 2.0

/-
# 4.4 Arrays and Indexing
-/

def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size
#eval northernTrees[2]

/-- A non-empty list -/
structure NonEmptyList (α: Type): Type where
  hd: α
  tl: List α
deriving BEq, Hashable, Repr

def NonEmptyList.get?: NonEmptyList α → Nat → Option α
  | lst, 0 => some lst.hd
  | lst, n + 1 => lst.get? n

abbrev NonEmptyList.inBounds (lst: NonEmptyList α) (n: Nat): Prop :=
  n ≤ lst.tl.length

def NonEmptyList.get (lst: NonEmptyList α) (n: Nat) (boundsCheck: inBounds lst n): α :=
  match n with
    | 0 => lst.hd
    | n + 1 => lst.tl[n]

instance: GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

def NonEmptyList.toList (l: NonEmptyList α): List α := l.hd :: l.tl

instance: Coe (NonEmptyList α) (List α) where
  coe := NonEmptyList.toList
instance: CoeDep (List α) (hd :: tl) (NonEmptyList α) where
  coe := ⟨hd, tl⟩

def NonEmptyList.append (l₁ l₂: NonEmptyList α): NonEmptyList α := ⟨l₁.hd, l₁.tl ++ l₂.hd :: l₂.tl⟩
def NonEmptyList.appendList (l₁: NonEmptyList α) (l₂: List α): List α := l₁.hd :: l₁.tl ++ l₂
def NonEmptyList.appendListNonEmpty (l₁: NonEmptyList α) (l₂: List α): NonEmptyList α := ⟨l₁.hd, l₁.tl ++ l₂⟩
def NonEmptyList.listAppend (l₁: List α) (l₂: NonEmptyList α): List α := l₁ ++ l₂
def NonEmptyList.listAppendNonEmpty (l₁: List α) (l₂: NonEmptyList α): NonEmptyList α :=
  match l₁ with
    | [] => l₂
    | hd::tl => ⟨hd, tl ++ l₂⟩

instance: Append (NonEmptyList α) where
  append := NonEmptyList.append
instance: HAppend (NonEmptyList α) (List α) (List α) where
  hAppend := NonEmptyList.appendList
instance: HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend := NonEmptyList.appendListNonEmpty
instance: HAppend (List α) (NonEmptyList α) (List α) where
  hAppend := NonEmptyList.listAppend
instance: HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend := NonEmptyList.listAppendNonEmpty

def NonEmptyList.map (f: α → β) (l: NonEmptyList α): NonEmptyList β := ⟨f l.hd, l.tl.map f⟩

instance: Functor NonEmptyList where
  map := NonEmptyList.map

private def boundsCheck {β: Type} [Coe β Nat] (lst: List α) (n: β): Prop :=
  lst.length > n

instance: GetElem (List α) ℙ α boundsCheck where
  getElem (lst: List α) (p: ℙ) _ := lst[p.toNat]
instance: GetElem (List α) ℙₙ α boundsCheck where
  getElem (lst: List α) (pₙ: ℙₙ) _ := lst[pₙ.toNat]
instance: GetElem (List α) 𝔼 α boundsCheck where
  getElem (lst: List α) (e: 𝔼) _ := lst[e.toNat]
instance: GetElem (List α) 𝕆 α boundsCheck where
  getElem (lst: List α) (o: 𝕆) _ := lst[o.toNat]

instance: GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p: PPoint α) (b: Bool) _ :=
    if b then p.x else p.y

def idahoSpiders: NonEmptyList String :=
  ⟨"Banded Garden Spider", ["Long-legged Sac Spider", "Wolf Spider", "Hobo Spider", "Cat-faced Spider"]⟩

theorem atLeastThreeSpiders:
  idahoSpiders.inBounds 2 := by simp
theorem notSixSpiders:
  ¬idahoSpiders.inBounds 5 := by simp

#eval idahoSpiders[3]

def lst: List Nat := [2, 4, 6, 8, 10]

def idxℙ: ℙ := 2
def idxℙₙ: ℙₙ := 2
def idx𝔼: 𝔼 := 2
def idx𝕆: 𝕆 := 1

#eval lst[idxℙ]
#eval lst[idxℙₙ]
#eval lst[idx𝔼]
#eval lst[idx𝕆]

#eval (⟨4.2, 2.7⟩: PPoint Float)[true]
#eval (⟨4.2, 2.7⟩: PPoint Float)[false]

/-
# 4.5 Standard Classes
-/


theorem funEq:
  (fun (x: Nat) => x + 1) = (Nat.succ ·) := by
    simp
theorem funEq2:
  (fun (x: Nat) => 1 + x) = (Nat.succ ·) := by
    simp [Nat.add_comm]

inductive BinTree (α: Type): Type where
  | leaf: BinTree α
  | branch: BinTree α → α → BinTree α → BinTree α
deriving BEq, Hashable, Repr

def BinTree.beq [BEq α]: BinTree α → BinTree α → Bool
  | .leaf, leaf => true
  | .branch t₁ₗ x₁ t₁ᵣ, .branch t₂ₗ x₂ t₂ᵣ =>
    x₁ == x₂ && beq t₁ₗ t₂ₗ && beq t₁ᵣ t₂ᵣ
  | _, _ => false

def BinTree.hash [Hashable α]: BinTree α → UInt64
  | .leaf => 0
  | .branch tₗ x tᵣ =>
    let hashᵣ := hash tᵣ
    let hashₓ := mixHash (Hashable.hash x) hashᵣ
    let hashₗ := mixHash (hash tₗ) hashₓ
    mixHash 1 hashₗ

def BinTree.map (f: α → β) (t: BinTree α): BinTree β :=
  match t with
    | .leaf => .leaf
    | .branch tₗ x tᵣ => .branch (tₗ.map f) (f x) (tᵣ.map f)

instance: Functor BinTree where
  map := BinTree.map

instance: Functor PPoint where
  map f p := ⟨f p.x, f p.y⟩

/-
# 4.6 Coercions
-/

structure Monoid where
  Carrier: Type
  neutral: Carrier
  op: Carrier → Carrier → Carrier

def Monoid.natMul: Monoid := ⟨Nat, 1, (· * ·)⟩
def Monoid.natAdd: Monoid := ⟨Nat, 0, (· + ·)⟩
def Monoid.string: Monoid := ⟨String, "", (· ++ ·)⟩
def Monoid.listMonoid (α: Type): Monoid := ⟨List α, [], (· ++ ·)⟩

instance: CoeSort Monoid Type where
  coe m := m.Carrier
instance: CoeDep Monoid M M.Carrier where
  coe := M.neutral
instance: CoeFun Monoid (fun m => m.Carrier → m.Carrier → m.Carrier) where
  coe m := m.op

def Monoid.foldMap (M: Monoid) (f: α → M) (l: List α): M :=
  let rec foldMap' (acc: M): List α → M
    | [] => acc
    | hd :: tl => foldMap' (M acc (f hd)) tl
  foldMap' M l

instance: CoeSort Bool Prop where
  coe b := b = true

structure Adder: Type where amt: Int

instance: CoeFun Adder (fun _ => Int → Int) where
  coe a := (· + a.amt)

def adder: Adder := ⟨42⟩
#eval adder 10

inductive JSON: Type where
  | null: JSON
  | true: JSON
  | false: JSON
  | number: Float → JSON
  | string: String → JSON
  | array: List JSON → JSON
  | object: List (String × JSON) → JSON
deriving BEq, Repr

structure Serializer where
  Contents: Type
  serialize: Contents → JSON

instance: CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def Str : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

#eval buildResponse "foo" Str "blah blah blah"
