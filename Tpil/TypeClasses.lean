/-
# Type Classes
-/

namespace TypeClasses

namespace Hidden
  structure Add (α: Type) where
    add: α → α → α

  #check @Add.add

  def double (s: Add α) (x: α): α :=
    s.add x x

  #eval double { add := Nat.add } 10
  #eval double { add := Nat.mul } 10
  #eval double { add := Int.add } (-10)
end Hidden

namespace TypeClasses
  class Add (α: Type u) where
    add: α → α → α

  #check @Add.add

  instance: Add Nat where
    add := Nat.add

  instance: Add Int where
    add := Int.add

  instance: Add Float where
    add := Float.add
end TypeClasses

def double [Add α] (x: α): α := x + x

#check @double
#eval double 10
#eval double (-10: Int)
#eval double (4.2: Float)
#eval double (239.0 + 2)

instance [Add α]: Add (Array α) where
  add a₁ a₂ := Array.zipWith a₁ a₂ (· + ·)

#eval Add.add #[1, 2] #[3, 4]
#eval #[1, 2] + #[3, 4]

namespace TypeClasses
  class Inhabited (α: Type u) where
    default: α

  #check @Inhabited.default

  instance: Inhabited Bool where
    default := true

  instance: Inhabited Nat where
    default := 0

  instance: Inhabited Unit where
    default := ()

  instance: Inhabited Prop where
    default := True

  #eval (Inhabited.default: Nat)
  #eval (Inhabited.default: Bool)
end TypeClasses

/-
## Chaining Instances
-/

namespace TypeClasses
  instance [Inhabited α] [Inhabited β]: Inhabited (α × β) where
    default := (Inhabited.default, Inhabited.default)

  #eval (Inhabited.default: Nat × Nat)

  -- instance [Inhabited β]: Inhabited (α → β) where
  --   default := fun _ => Inhabited.default

  #check (inferInstance: Inhabited Nat)

  def foo: Inhabited (Nat × Nat) := inferInstance

  example: foo.default = (Inhabited.default, Inhabited.default) := rfl

  #print inferInstance
end TypeClasses

/-
## ToString
-/

structure Person where
  name: String
  age: Nat

instance: ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542: Person }
#eval toString ({ name := "Daniel", age := 18 }: Person)

/-
## Numerals
-/

structure Rational where
  num: Int
  den: Int
  inv: den ≠ 0

instance: OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance: ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2: Rational)

#check (2: Rational)
#check (2: Nat)

#check nat_lit 2

class Monoid (α: Type u) where
  unit: α
  op: α → α → α

instance [s: Monoid α]: OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α]: α := 1

/-
## Output Parameters
-/

#check_failure (inferInstance: Inhabited (Nat × _))

namespace TypeClasses
  class HMul (α: Type u) (β: Type v) (γ: outParam (Type w)) where
    hMul: α → β → γ

  instance: HMul Nat Nat Nat where
    hMul := Nat.mul

  instance: HMul Nat (Array Nat) (Array Nat) where
    hMul n a := a.map (fun x => HMul.hMul n x)

  #eval HMul.hMul 4 3
  #eval HMul.hMul 4 #[2, 3, 4]

  instance: HMul Int Int Int where
    hMul := Int.mul

  instance [HMul α β γ]: HMul α (Array β) (Array γ) where
    hMul x a := a.map (fun e => HMul.hMul x e)

  #eval HMul.hMul 4 3
  #eval HMul.hMul 4 #[2, 3, 4]
  #eval HMul.hMul (-2) #[3, -1, 4]
  #eval HMul.hMul 2 #[#[2, 3], #[0, 4]]
end TypeClasses

/-
## Default Instances
-/

namespace TypeClasses
  def xs: List Int := [1, 2, 3]

  #check_failure fun y => xs.map (fun x => HMul.hMul x y)

  @[default_instance]
  instance: HMul Int Int Int where
    hMul := Int.mul

  #check fun y => xs.map (fun x => HMul.hMul x y)

  @[default_instance 200]
  instance: OfNat Rational n where
    ofNat := { num := n, den := 1, inv := by decide }

  #check 2

  @[default_instance]
  instance (n: Nat): OfNat Nat n where
    ofNat := n

  class Mul (α: Type u) where
    mul: α → α → α

  @[default_instance 10]
  instance [Mul α]: HMul α α α where
    hMul := Mul.mul
end TypeClasses

/-
## Local Instances
-/

structure Point where
  x : Nat
  y : Nat

section
  local instance: Add Point where
    add p₁ p₂ := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

  def doublePoint (p: Point) := p + p

  local instance addPoint: Add Point where
    add p₁ p₂ := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

  attribute [-instance] addPoint
end

/-
## Scoped Instances
-/

namespace Point
  scoped instance: Add Point where
    add p₁ p₂ := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

  def double (p: Point) := p + p
end Point

#check_failure fun (p: Point) => p + p + p

namespace Point
  #check fun (p: Point) => p + p + p
end Point

open scoped Point

#check fun (p: Point) => p + p + p

/-
## Decidable Propositions
-/

namespace TypeClasses
  class inductive Decidable (p: Prop) where
    | isFalse (h: ¬p): Decidable p
    | isTrue (h: p): Decidable p

  def ite {α: Sort u} (c: Prop) [h: Decidable c] (t e: α): α :=
    Decidable.casesOn
      (motive := fun _ => α)
      h
      (fun _ => e)
      (fun _ => t)

  def dite {α: Sort u} (c: Prop) [h: Decidable c] (t: c → α) (e: Not c → α): α :=
    Decidable.casesOn (motive := fun _ => α) h e t
end TypeClasses

#check @instDecidableAnd
#check @instDecidableOr
#check @instDecidableNot

def step (a b x: Nat): Nat :=
  if x < a ∧ x > b
  then 0
  else 1

section
  set_option pp.explicit true
  #print step
end

namespace TypeClasses
  open Classical

  noncomputable scoped instance (priority := low) propDecidable (a: Prop): Decidable a :=
    choice <| match em a with
      | Or.inl h => ⟨Decidable.isTrue h⟩
      | Or.inr h => ⟨Decidable.isFalse h⟩

  example: 10 < 5 ∨ 1 > 0 := by decide
  example: ¬(True ∧ False) := by decide
  example: 10 * 20 = 200 := by decide

  theorem ex: True ∧ 2 = 1 + 1 := by decide
  #print ex

  #check of_decide_eq_true
  #check @decide
end TypeClasses

/-
## Managing Type Class Inference
-/

def foo: Add Nat := inferInstance
def bar: Inhabited (Nat → Nat) := inferInstance

#check @inferInstance
#check (inferInstance: Add Nat)

#check inferInstanceAs (Add Nat)
#check @inferInstanceAs

def Set (α: Type u) := α → Prop

instance: Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))

example: Inhabited (Set α) := inferInstance

section
  set_option trace.Meta.synthInstance true

  set_option synthInstance.maxHeartbeats 10000
  set_option synthInstance.maxSize 400
end

class Foo where
  a: Nat
  b: Nat

instance (priority := default + 1) i1: Foo where
  a := 1
  b := 1

instance i2: Foo where
  a := 2
  b := 2

example: Foo.a = 1 := rfl

instance (priority := default + 2) i3: Foo where
  a := 3
  b := 3

example: Foo.a = 3 := rfl

/-
## Coercions Using Type Classes
-/

instance: Coe Bool Prop where
  coe b := b = true

#eval if true then 5 else 3
#eval if false then 5 else 3

/-
def List.toSet: List α → Set α
  | [] => Set.empty
  | hd::tl => {hd} ∪ tl.toSet

instance: Coe (List α) (Set α) where
  coe l := l.toSet

def s: Set Nat := {1}
#check s ∪ [2, 3]

#check let x := ↑[2, 3]; s ∪ x
#check let x := [2, 3]; s ∪ x
-/

instance (p: Prop) [Decidable p]: CoeDep Prop p Bool where
  coe := decide p

structure Semigroup where
  carrier: Type u
  mul: carrier → carrier → carrier
  mul_assoc (a b c: carrier): mul (mul a b) c = mul a (mul b c)

instance (S: Semigroup): Mul S.carrier where
  mul a b := S.mul a b

#check Semigroup.carrier

instance: CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S: Semigroup) (a b c: S): (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc S a b c

structure Morphism (S₁ S₂: Semigroup) where
  mor: S₁ → S₂
  resp_mul: ∀ a b: S₁, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor

instance (S₁ S₂: Semigroup): CoeFun (Morphism S₁ S₂) (fun _ => S₁ → S₂) where
  coe m := m.mor

theorem resp_mul {S₁ S₂: Semigroup} (f: Morphism S₁ S₂) (a b: S₁): f (a * b) = (f a) * (f b) :=
  f.resp_mul a b

example (S₁ S₂: Semigroup) (f: Morphism S₁ S₂) (x: S₁): f (x * x * x) = f x * f x * f x :=
  calc f (x * x * x)
    _ = f (x * x) * f x := by rw [resp_mul f]
    _ = f x * f x * f x := by rw [resp_mul f]

end TypeClasses
