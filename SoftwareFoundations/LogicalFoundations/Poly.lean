/-
# Polymorphism and Higher-Order Functions
-/

import «SoftwareFoundations».«LogicalFoundations».«Lists»

namespace MumbleGrumble
  inductive Mumble: Type where
    | a: Mumble
    | b: Mumble → Nat → Mumble
    | c: Mumble
  deriving Repr

  inductive Grumble (α: Type): Type where
    | d: Mumble → Grumble α
    | e: α → Grumble α

  #check Grumble.d (Mumble.b Mumble.a 5)
  #check @Grumble.d Mumble (Mumble.b Mumble.a 5)
  #check @Grumble.d Bool (Mumble.b Mumble.a 5)
  #check Grumble.e true
  #check @Grumble.e Mumble (Mumble.b Mumble.c 0)
  -- Not well-typed
  -- #check @Grumble.e Bool (Mumble.b Mumble.c 0)
  #check Mumble.c
end MumbleGrumble

/-
## Polymorphic Lists
-/

inductive BoolList: Type where
  | nil: BoolList
  | cons: Bool → BoolList → BoolList

inductive PolyList (α: Type): Type where
  | nil: PolyList α
  | cons: α → PolyList α → PolyList α
deriving Repr

def PolyList.rpt (v: α): Nat → PolyList α
  | .zero => .nil
  | .succ n => .cons v (rpt v n)

def PolyList.append: PolyList α → PolyList α → PolyList α
  | .nil, l | l, .nil => l
  | .cons hd tl, l => .cons hd (tl.append l)

def PolyList.rev: PolyList α → PolyList α
  | .nil => .nil
  | .cons hd tl => tl.rev.append (.cons hd nil)

def PolyList.length: PolyList α → Nat
  | .nil => 0
  | .cons _ tl => 1 + tl.length

example: PolyList.rpt 4 2 = .cons 4 (.cons 4 .nil) := by rfl
example: PolyList.rpt false 1 = .cons false .nil := by rfl

example: (PolyList.cons 1 (.cons 2 .nil)).rev = (PolyList.cons 2 (.cons 1 .nil)) := by rfl
example: (PolyList.cons true .nil).rev = (PolyList.cons true .nil) := by rfl
example: (PolyList.cons 1 (.cons 2 (.cons 3 .nil))).length = 3 := by rfl

def MyNil := @PolyList.nil Nat

/-
#### Exercises
-/

@[simp]
theorem PolyList.appNilLeft (l: PolyList α): PolyList.nil.append l = l := by
  cases l <;> rfl

@[simp]
theorem PolyList.appNilRight (l: PolyList α): l.append .nil = l := by
  cases l <;> rfl

@[simp]
theorem PolyList.appAssoc (l₁ l₂ l₃: PolyList α): (l₁.append l₂).append l₃ = l₁.append (l₂.append l₃) := by
  sorry
  -- induction l₁ with
  --   | nil => simp
  --   | cons hd tl ihₗ =>
  --     rw [PolyList.append, PolyList.append, PolyList.append]
  --     rw [ihₗ]

@[simp]
theorem PolyList.appLength (l₁ l₂: PolyList α): (l₁.append l₂).length = l₁.length + l₂.length := by
  sorry
  -- induction l₁ with
  --   | nil => simp
  --   | cons hd tl ihₗ =>
  --     rw [PolyList.length, PolyList.append, PolyList.length]
  --     rw [ihₗ]
  --     simp [Nat.add_assoc]

@[simp]
theorem PolyList.revAppDistr (l₁ l₂: PolyList α): (l₁.append l₂).rev = l₂.rev.append l₁.rev := by
  sorry
  -- induction l₁ with
  --   | nil => simp
  --   | cons hd tl ihₗ =>
  --     rw [PolyList.rev, PolyList.append, PolyList.rev]
  --     rw [ihₗ]
  --     simp [PolyList.appAssoc]

@[simp]
theorem PolyList.revInvolute (l: PolyList α): l.rev.rev = l := by
  sorry
  -- induction l with
  --   | nil => simp
  --   | cons hd tl ihₗ =>
  --     simp
  --     rw [ihₗ]
  --     rw [PolyList.append, PolyList.appNilLeft]

/-
### Polymorphic Pairs
-/

structure PolyProd (α β: Type): Type where
  a: α
  b: β
deriving Repr

def PolyProd.fst (p: PolyProd α β): α := p.1
def PolyProd.snd (p: PolyProd α β): β := p.2

def PolyList.zip: PolyList α → PolyList β → PolyList (PolyProd α β)
  | .nil, _ | _, .nil => .nil
  | .cons hd₁ tl₁, .cons hd₂ tl₂ => .cons ⟨hd₁, hd₂⟩ (tl₁.zip tl₂)

/-
#### Exercises
-/

#check @PolyList.zip
#eval (PolyList.cons 1 (.cons 2 .nil)).zip (PolyList.cons false (.cons false (.cons true (.cons true .nil))))

def PolyList.split: PolyList (PolyProd α β) → PolyProd (PolyList α) (PolyList β)
  | .nil => ⟨.nil, .nil⟩
  | .cons hd tl =>
    let ⟨tl₁, tl₂⟩ := tl.split
    ⟨.cons hd.fst tl₁, .cons hd.snd tl₂⟩

example: (PolyList.cons (⟨1, false⟩: PolyProd Nat Bool) (.cons ⟨2, false⟩ .nil)).split = ⟨.cons 1 (.cons 2 .nil), .cons false (.cons false .nil)⟩ := by rfl

/-
### Polymorphic Options
-/

inductive PolyOption (α: Type): Type where
  | none: PolyOption α
  | some: α → PolyOption α
deriving Repr

def PolyList.nthOpt: Nat → PolyList α → PolyOption α
  | _, .nil => .none
  | .zero, .cons hd _ => .some hd
  | .succ n, .cons _ tl => tl.nthOpt n

example: (PolyList.cons 4 (.cons 5 (.cons 6 (.cons 7 .nil)))).nthOpt 0 = .some 4 := by rfl
example: (PolyList.cons (PolyList.cons 1 .nil) (.cons (.cons 2 .nil) .nil)).nthOpt 1 = .some (.cons 2 .nil) := by rfl
example: (PolyList.cons true .nil).nthOpt 2 = .none := by rfl

def PolyList.hdOpt: PolyList α → PolyOption α
  | .nil => .none
  | .cons hd _ => .some hd

example: (PolyList.cons 1 (.cons 2 .nil)).hdOpt = .some 1 := by rfl
example: (PolyList.cons (PolyList.cons 1 .nil) (.cons (.cons 2 .nil) .nil)).hdOpt = .some (.cons 1 .nil) := by rfl
example: (@PolyList.nil Nat).hdOpt = .none := by rfl

/-
## Functions As Data
-/

def threeTimes (f: α → α) (n: α): α :=
  (f ∘ f ∘ f) n

example: threeTimes Nat.minusTwo 9 = 3 := by rfl
example: threeTimes 𝔹.neg .true = .false := by rfl

def PolyList.filter (p: α → Bool): PolyList α → PolyList α
  | .nil => .nil
  | .cons hd tl =>
    if p hd
    then .cons hd (tl.filter p)
    else tl.filter p

example: (PolyList.cons 1 (.cons 2 (.cons 3 (.cons 4 .nil)))).filter Nat.isEven = .cons 2 (.cons 4 .nil) := by rfl

def PolyList.isSingleton (l: PolyList α): Bool :=
  l.length == 1

def PolyList.singletons (l: PolyList (PolyList α)): PolyList (PolyList α) :=
  l.filter PolyList.isSingleton

example: (PolyList.cons (PolyList.cons 1 (.cons 2 .nil)) (.cons (.cons 3 .nil) (.cons (.cons 4 .nil) (.cons (.cons 5 (.cons 6 (.cons 7 .nil))) (.cons .nil (.cons (.cons 8 .nil) .nil)))))).singletons = .cons (.cons 3 .nil) (.cons (.cons 4 .nil) (.cons (.cons 8 .nil) .nil)) := by rfl

def PolyList.countOddMembers (l: PolyList Nat): Nat :=
  (l.filter Nat.isOdd).length

example: (PolyList.cons 1 (.cons 0 (.cons 3 (.cons 1 (.cons 4 (.cons 5 .nil)))))).countOddMembers = 4 := by rfl
example: (PolyList.cons 0 (.cons 2 (.cons 4 .nil))).countOddMembers = 0 := by rfl
example: PolyList.nil.countOddMembers = 0 := by rfl

/-
### Anonymous Functions
-/

example: threeTimes (· ^ 2) 2 = 256 := by rfl

example: (PolyList.cons (PolyList.cons 1 (.cons 2 .nil)) (.cons (.cons 3 .nil) (.cons (.cons 4 .nil) (.cons (.cons 5 (.cons 6 (.cons 7 .nil))) (.cons .nil (.cons (.cons 8 .nil) .nil)))))).filter (·.length == 1) = .cons (.cons 3 .nil) (.cons (.cons 4 .nil) (.cons (.cons 8 .nil) .nil)) := by rfl

/-
#### Exercises
-/

def PolyList.evenGt₇ (l: PolyList Nat): PolyList Nat :=
  (l.filter (· > 7)).filter (·.isEven)

example: (PolyList.cons 1 (.cons 2 (.cons 6 (.cons 9 (.cons 10 (.cons 3 (.cons 12 (.cons 8 .nil)))))))).evenGt₇ = .cons 10 (.cons 12 (.cons 8 .nil)) := by rfl
example: (PolyList.cons 5 (.cons 2 (.cons 6 (.cons 19 (.cons 129 .nil))))).evenGt₇ = .nil := by rfl

def PolyList.partition (p: α → Bool): PolyList α → PolyProd (PolyList α) (PolyList α)
  | .nil => ⟨.nil, .nil⟩
  | .cons hd tl =>
    let ⟨tl₁, tl₂⟩ := tl.partition p
    if p hd
    then ⟨.cons hd tl₁, tl₂⟩
    else ⟨tl₁, .cons hd tl₂⟩

example: (PolyList.cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil))))).partition Nat.isOdd = ⟨.cons 1 (.cons 3 (.cons 5 .nil)), .cons 2 (.cons 4 .nil)⟩ := by rfl
example: (PolyList.cons 5 (.cons 9 (.cons 0 .nil))).partition (λ _ => false) = ⟨.nil, (PolyList.cons 5 (.cons 9 (.cons 0 .nil)))⟩ := by rfl

def PolyList.map (f: α → β): PolyList α → PolyList β
  | .nil => .nil
  | .cons hd tl => .cons (f hd) (tl.map f)

example: (PolyList.cons 2 (.cons 0 (.cons 2 .nil))).map (3 + ·) = .cons 5 (.cons 3 (.cons 5 .nil)) := by rfl
example: (PolyList.cons 2 (.cons 1 (.cons 2 (.cons 5 .nil)))).map Nat.isOdd = .cons false (.cons true (.cons false (.cons true .nil))) := by rfl
example: (PolyList.cons 2 (.cons 1 (.cons 2 (.cons 5 .nil)))).map (λ n => (PolyList.cons (n.isEven) (.cons (n.isOdd) .nil))) = .cons (.cons true (.cons false .nil)) (.cons (.cons false (.cons true .nil)) (.cons (.cons true (.cons false .nil)) (.cons (.cons false (.cons true .nil)) .nil))) := by rfl

def PolyList.mapRev (f: α → β): PolyList α → PolyList β
  | .nil => .nil
  | .cons hd tl => (tl.mapRev f).append (.cons (f hd) .nil)

def PolyList.flatMap (f: α → PolyList β): PolyList α → PolyList β
  | .nil => .nil
  | .cons hd tl => (f hd).append (tl.flatMap f)

example: (PolyList.cons 1 (.cons 5 (.cons 4 .nil))).flatMap (λ n => (PolyList.cons n (.cons n (.cons n .nil)))) = .cons 1 (.cons 1 (.cons 1 (.cons 5 (.cons 5 (.cons 5 (.cons 4 (.cons 4 (.cons 4 .nil)))))))) := by rfl

def PolyOption.map (f: α → β): PolyOption α → PolyOption β
  | .none => .none
  | .some v => .some (f v)

/-
### Fold
-/

def PolyList.fold (f: α → β → β): PolyList α → β → β
  | .nil, acc => acc
  | .cons hd tl, acc => f hd (tl.fold f acc)

example: (PolyList.cons 1 (.cons 2 (.cons 3 (.cons 4 .nil)))).fold Nat.mul 1 = 24 := by rfl
example: (PolyList.cons .true (.cons .true (.cons .false (.cons .true .nil)))).fold 𝔹.and .true = .false := by rfl
example: (PolyList.cons (.cons 1 .nil) (.cons .nil (.cons (.cons 2 (.cons 3 .nil)) (.cons (.cons 4 .nil) .nil)))).fold PolyList.append .nil = .cons 1 (.cons 2 (.cons 3 (.cons 4 .nil))) := by rfl

/-
### Functions That Construct Functions
-/

def const (x: α): Nat → α :=
  λ _ => x

def constTrue: Nat → Bool := const true

example: constTrue 0 = true := by rfl
example: (const 5) 99 = 5 := by rfl

def Nat.plus3: Nat → Nat := (· + 3)

example: (4).plus3 = 7 := by rfl
example: threeTimes Nat.plus3 0 = 9 := by rfl
example: threeTimes (Nat.add 3) 0 = 9 := by rfl

/-
## Additional Exercises
-/

def PolyList.foldLength (l: PolyList α): Nat :=
  l.fold (λ _ acc => acc + 1) 0

example: (PolyList.cons 4 (.cons 7 (.cons 0 .nil))).foldLength = 3 := by rfl

theorem PolyList.foldLengthCorrect (l: PolyList α): l.foldLength = l.length := by
  induction l with
    | nil => rfl
    | cons hd tl ihₗ =>
      rw [PolyList.foldLength] at ihₗ
      rw [PolyList.length, PolyList.foldLength, PolyList.fold]
      rw [ihₗ]
      rw [Nat.add_comm]

def PolyList.foldMap (f: α → β) (l: PolyList α): PolyList β :=
  l.fold (λ hd acc => .cons (f hd) acc) .nil

example: (PolyList.cons 1 (.cons 2 (.cons 3 .nil))).foldMap (· * 2) = .cons 2 (.cons 4 (.cons 6 .nil)) := by rfl

def curry (f: PolyProd α β → γ): α → β → γ :=
  λ a => λ b => f ⟨a, b⟩

def uncurry (f: α → β → γ): PolyProd α β → γ :=
  λ ⟨a, b⟩ => f a b

#check @curry
#check @uncurry

theorem uncurryCurry (f: α → β → γ) (x: α) (y: β): curry (uncurry f) x y = f x y := by
  rw [curry, uncurry]
theorem curryUncurry (f: PolyProd α β → γ) (p: PolyProd α β): uncurry (curry f) p = f p := by
  rw [uncurry]
  sorry

/-
### Church Numerals (Advanced)
-/

namespace Church
  def CNat (α: Type): Type := (α → α) → α → α

  def CNat.zero: CNat α := λ (_: α → α) (zero: α) => zero
  def CNat.one: CNat α := λ (succ: α → α) (zero: α) => succ zero
  def CNat.two: CNat α := λ (succ: α → α) (zero: α) => succ (succ zero)
  def CNat.three: CNat α := λ (succ: α → α) (zero: α) => succ (succ (succ zero))

  example: CNat.zero Nat.succ Nat.zero = 0 := by rfl
  example: CNat.one Nat.succ Nat.zero = 1 := by rfl
  example: CNat.two Nat.succ Nat.zero = 2 := by rfl

  def CNat.succ (n: CNat α): CNat α :=
    λ (succ: α → α) (zero: α) => succ (n succ zero)

  example (α: Type): @CNat.succ α CNat.zero = CNat.one := by rfl
  example (α: Type): @CNat.succ α CNat.one = CNat.two := by rfl
  example (α: Type): @CNat.succ α CNat.two = CNat.three := by rfl

  def CNat.add (n₁ n₂: CNat α): CNat α :=
    sorry

  -- example (α: Type): CNat.add α CNat.zero CNat.one = CNat.one := by rfl
  -- example (α: Type): CNat.add α CNat.two CNat.three = CNat.add α CNat.three CNat.two := by rfl
  -- example (α: Type): CNat.add α (CNat.add α CNat.two CNat.two) CNat.three = CNat.add α CNat.one (CNat.add α CNat.three CNat.three) := by rfl

  def CNat.mul (n₁ n₂: CNat α): CNat α :=
    sorry

  -- example (α: Type): CNat.mul α CNat.one CNat.one = CNat.one := by rfl
  -- example (α: Type): CNat.mul α CNat.zero (CNat.add α CNat.three CNat.three) = CNat.zero := by rfl
  -- example (α: Type): CNat.mul α CNat.two CNat.three = CNat.mul α CNat.three CNat.two := by rfl

  def CNat.pow (n₁ n₂: CNat α): CNat α :=
    sorry

  -- example (α: Type): @CNat.pow α CNat.two CNat.two = CNat.add α CNat.two CNat.two := by rfl
  -- example (α: Type): @CNat.pow α CNat.three CNat.zero = CNat.one := by rfl
  -- example (α: Type): @CNat.pow α CNat.three CNat.two = CNat.add α (CNat.mul α CNat.two (CNat.mul α CNat.two CNat.two)) CNat.one := by rfl
end Church
