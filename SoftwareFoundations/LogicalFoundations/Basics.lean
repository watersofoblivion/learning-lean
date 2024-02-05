/-
# Basics
-/

/-
## Data And Functions
-/

/-
### Days of the week
-/

inductive Day: Type where
  | monday: Day
  | tuesday: Day
  | wednesday: Day
  | thursday: Day
  | friday: Day
  | saturday: Day
  | sunday: Day
deriving Repr

def Day.nextWeekday: Day -> Day
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | _ => .monday

#eval Day.friday.nextWeekday
#eval Day.saturday.nextWeekday.nextWeekday

example: Day.saturday.nextWeekday.nextWeekday = Day.tuesday := by rfl

/-
### Booleans
-/

inductive 𝔹: Type where
  | true
  | false

def 𝔹.and: 𝔹 → 𝔹 → 𝔹
  | .true, .true => .true
  | _, _ => .false

def 𝔹.or: 𝔹 → 𝔹 → 𝔹
  | .false, .false => .false
  | _, _ => .true

def 𝔹.neg: 𝔹 → 𝔹
  | .true => .false
  | .false => .true

example: 𝔹.and .true .true = .true := by rfl
example: 𝔹.and .true .false = .false := by rfl
example: 𝔹.and .false .false = .false := by rfl
example: 𝔹.and .false .true = .false := by rfl

example: 𝔹.or .true .false = .true := by rfl
example: 𝔹.or .false .false = .false := by rfl
example: 𝔹.or .false .true = .true := by rfl
example: 𝔹.or .true .true = .true := by rfl

example: 𝔹.neg .true = .false := by rfl
example: 𝔹.neg .false = .true := by rfl

/-
#### Exercises
-/

/-- Exercise: nand -/
def 𝔹.nand (b₁ b₂: 𝔹): 𝔹 := (𝔹.and b₁ b₂).neg

example: 𝔹.nand .true .true = .false := by rfl
example: 𝔹.nand .true .false = .true := by rfl
example: 𝔹.nand .false .false = .true := by rfl
example: 𝔹.nand .false .true = .true := by rfl

/-- Exercise: and3 -/
def and3 (b₁ b₂ b₃: 𝔹): 𝔹 := (b₁.and b₂).and b₃

example: and3 .true .true .true = .true := by rfl
example: and3 .true .true .false = .false := by rfl
example: and3 .true .false .true = .false := by rfl
example: and3 .true .false .false = .false := by rfl
example: and3 .false .true .true = .false := by rfl
example: and3 .false .true .false = .false := by rfl
example: and3 .false .false .true = .false := by rfl
example: and3 .false .false .false = .false := by rfl

/-
### Types
-/

#check 𝔹.true
#check (𝔹.true: 𝔹)
#check 𝔹.neg .true

/-
### New Types from Old
-/

inductive RGB: Type where
  | red: RGB
  | green: RGB
  | blue: RGB

inductive Color: Type where
  | black: Color
  | white: Color
  | primary: RGB → Color

def monochrome: Color → 𝔹
  | .black | .white => .true
  | _ => .false

def isRed: Color → 𝔹
  | .primary .red => .true
  | _ => .false

/-
### Namespaces (Modules in LF)
-/

namespace Playground
  def foo: RGB := .blue
end Playground

def foo: 𝔹 := .true

#check Playground.foo
#check foo

/-
### Structures (Tuples in LF)
-/

namespace TuplePlayground
  inductive Bit: Type where
    | b₀
    | b₁

  structure Nybble: Type where
    b₀: Bit
    b₁: Bit
    b₂: Bit
    b₃: Bit

  #check (⟨.b₀, .b₁, .b₀, .b₁⟩: Nybble)

  def Nybble.allZeros: Nybble → Bool
    | ⟨.b₀, .b₀, .b₀, .b₀⟩ => true
    | _ => false

  example: (⟨.b₀, .b₀, .b₀, .b₀⟩: Nybble).allZeros = .true := by rfl
  example: (⟨.b₀, .b₁, .b₀, .b₁⟩: Nybble).allZeros = .false := by rfl
end TuplePlayground

/-
### Numbers
-/

namespace NatPlayground
  inductive ℕ: Type where
    | zero: ℕ
    | succ: ℕ → ℕ

  def ℕ.pred: ℕ → ℕ
    | .zero => .zero
    | .succ n => n

  def zero: ℕ := ℕ.zero
  def one: ℕ := ℕ.succ zero
  def two: ℕ := ℕ.succ one

  example: zero.pred = zero := by rfl
  example: one.pred = zero := by rfl
  example: two.pred = one := by rfl
end NatPlayground

def Nat.minusTwo: Nat → Nat
  | .zero => .zero
  | .succ .zero => .zero
  | .succ (.succ n) => n

example: (0: Nat).minusTwo = 0 := by rfl
example: (1: Nat).minusTwo = 0 := by rfl
example: (2: Nat).minusTwo = 0 := by rfl
example: (3: Nat).minusTwo = 1 := by rfl
example: (4: Nat).minusTwo = 2 := by rfl

#check Nat.succ
#check NatPlayground.ℕ.pred
#check Nat.minusTwo

def Nat.isEven: Nat → Bool
  | .zero => .true
  | .succ .zero => .false
  | .succ (.succ n) => n.isEven

example: (0: Nat).isEven = .true := by rfl
example: (1: Nat).isEven = .false := by rfl
example: (2: Nat).isEven = .true := by rfl
example: (3: Nat).isEven = .false := by rfl

def Nat.isOdd (n: Nat): Bool := ¬n.isEven

example: (0: Nat).isOdd = .false := by rfl
example: (1: Nat).isOdd = .true := by rfl
example: (2: Nat).isOdd = .false := by rfl
example: (3: Nat).isOdd = .true := by rfl

namespace NatPlayground2
  def Nat.plus: Nat → Nat → Nat
    | .zero, n => n
    | .succ n₁, n₂ => .succ (plus n₁ n₂)

  example: Nat.plus 0 0 = 0 := by rfl
  example: Nat.plus 0 1 = 1 := by rfl
  example: Nat.plus 1 0 = 1 := by rfl
  example: Nat.plus 1 1 = 2 := by rfl

  def Nat.times: Nat → Nat → Nat
    | .zero, _ | _, .zero => 0
    | .succ n₁, n₂ => plus (times n₁ n₂) n₂

  example: Nat.times 0 42 = 0 := by rfl
  example: Nat.times 42 0 = 0 := by rfl
  example: Nat.times 1 42 = 42 := by rfl
  example: Nat.times 42 1 = 42 := by rfl
  example: Nat.times 10 5 = 50 := by rfl

  def Nat.minus: Nat → Nat → Nat
    | .zero, _ => 0
    | n, .zero => n
    | .succ n₁, .succ n₂ => minus n₁ n₂

  example: Nat.minus 0 0 = 0 := by rfl
  example: Nat.minus 3 2 = 1 := by rfl
  example: Nat.minus 2 3 = 0 := by rfl
end NatPlayground2

def exp (base pow: Nat): Nat :=
  match pow with
    | .zero => 1
    | .succ p => base * (exp base p)

def Nat.eq: Nat → Nat → Bool
  | .zero, .zero => true
  | .succ n₁, .succ n₂ => eq n₁ n₂
  | _, _ => false

example: Nat.eq 0 0 = true := by rfl
example: Nat.eq 1 0 = false := by rfl
example: Nat.eq 0 1 = false := by rfl
example: Nat.eq 42 42 = true := by rfl

def Nat.less_eq: Nat → Nat → Bool
  | .zero, _ => true
  | .succ _, .zero => false
  | .succ n₁, .succ n₂ => less_eq n₁ n₂

example: Nat.less_eq 0 0 = true := by rfl
example: Nat.less_eq 0 1 = true := by rfl
example: Nat.less_eq 42 42 = true := by rfl
example: Nat.less_eq 21 42 = true := by rfl
example: Nat.less_eq 1 0 = false := by rfl
example: Nat.less_eq 42 21 = false := by rfl

/-
#### Exercises
-/

/- Exercise: Factorial -/
def Nat.factorial (n: Nat): Nat :=
  match n with
    | .zero => 1
    | .succ n' => n * factorial n'

example: Nat.factorial 0 = 1 := by rfl
example: Nat.factorial 1 = 1 := by rfl
example: Nat.factorial 2 = 2 := by rfl
example: Nat.factorial 3 = 6 := by rfl
example: Nat.factorial 4 = 24 := by rfl
example: Nat.factorial 5 = 120 := by rfl

/- Exercise: Less Than -/

def Nat.less (n₁ n₂: Nat): Bool := Nat.less_eq n₁ n₂ && !(Nat.eq n₁ n₂)

example: Nat.less 0 0 = false := by rfl
example: Nat.less 0 1 = true := by rfl
example: Nat.less 42 42 = false := by rfl
example: Nat.less 21 42 = true := by rfl
example: Nat.less 1 0 = false := by rfl
example: Nat.less 42 21 = false := by rfl

/-
## Proof By Simplification
-/

example (n: Nat): 0 + n = n := by simp
example (n: Nat): 1 + n = .succ n := by
  rw [Nat.add_comm]
example (n: Nat): 0 * n = 0 := by simp
example (n₁ n₂: Nat): (n₁ * 0) + (n₂ * 0) = 0 := by simp

/-
## Proof By Rewriting
-/

example (n₁ n₂: Nat) (h: n₁ = n₂): n₁ + n₁ = n₂ + n₂ := by
  rw [h]

/-
#### Exercises
-/

example (n₁ n₂ n₃: Nat) (h₁: n₁ = n₂) (h₂: n₂ = n₃): n₁ + n₂ = n₂ + n₃ := by
  rw [h₁, h₂]
example (n: Nat): n * 1 = n := by simp

/-
# Proof By Case Analysis
-/

example (n: Nat): Nat.eq (n + 1) 0 = false := by
  cases n <;> rfl

theorem 𝔹.neg_involute (b: 𝔹): b.neg.neg = b := by
  cases b <;> rfl

example (b₁ b₂: 𝔹): 𝔹.and b₁ b₂ = 𝔹.and b₂ b₁ := by
  cases b₁ <;> cases b₂ <;> rfl

example (b₁ b₂ b₃: 𝔹): (𝔹.and b₁ b₂).and b₃ = (𝔹.and b₁ b₃).and b₂ := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-
#### Exercises
-/

/- Exercise: andTrueElim -/
example (b₁ b₂: 𝔹) (h: 𝔹.and b₁ b₂ = .true): b₂ = .true := by
  cases b₁ with
    | true =>
      cases b₂ with
        | true => simp
        | false => contradiction
    | false =>
      cases b₂ with
        | true => rw [← h]
        | false => contradiction

/- Exercise: zeroNeqPlusOne -/
example (n: Nat): !(Nat.eq 0 (n + 1)) := by
  simp
  cases n <;> first | simp | rfl

/-
## More Exercises
-/

example (f: 𝔹 → 𝔹) (h: ∀ x: 𝔹, f x = x) (b: 𝔹): (f ∘ f) b = b := by
  simp
  cases b <;> (rw [h]; rw [h])

example (f: 𝔹 → 𝔹) (h: ∀ x: 𝔹, f x = 𝔹.neg x) (b: 𝔹): (f ∘ f) b = b := by
  simp
  cases b <;> (rw [h]; rw [h]; rfl)

example (b₁ b₂: 𝔹): b₁.and b₂ = b₁.or b₂ → b₁ = b₂ := by
  cases b₁ with
    | true =>
      cases b₂ with
        | true => simp
        | false => simp [𝔹.and, 𝔹.or]
    | false =>
      cases b₂ with
        | true => simp [𝔹.and, 𝔹.or]
        | false => simp

/-
### Course Late Policies, Formalized
-/

namespace LateDays
  inductive Letter: Type where
    | a: Letter
    | b: Letter
    | c: Letter
    | d: Letter
    | f: Letter
  deriving Repr

  def Letter.compare: Letter → Letter → Ordering
    | .a, .a | .b, .b | .c, .c | .d, .d | .f, .f => .eq
    | .a, _ => .gt
    | .b, .a => .lt
    | .b, _ => .gt
    | .c, .a | .c, .b => .lt
    | .c, _ => .gt
    | .d, .a | .d, .b | .d, .c => .lt
    | .d, _ => .gt
    | .f, _ => .lt

  def Letter.lower: Letter → Letter
    | .a => .b
    | .b => .c
    | .c => .d
    | _ => .f

  def Letter.canLower: Letter → Bool
    | .f => false
    | _ => true

  @[simp]
  theorem Letter.eq (l: Letter): Letter.compare l l = Ordering.eq := by
    cases l <;> rfl

  @[simp]
  theorem Letter.lowerF: Letter.f.lower = Letter.f := by rfl

  @[simp]
  theorem Letter.lowerNonF (l: Letter) (h: Letter.compare Letter.f l = Ordering.lt): l.lower.compare l = Ordering.lt := by
      cases l with
        | a => rfl
        | b => rfl
        | c => rfl
        | d => rfl
        | f =>
          rw [←h]
          rfl

  example: Letter.compare Letter.a Letter.a = Ordering.eq := by rfl
  example: Letter.compare Letter.a Letter.b = Ordering.gt := by rfl
  example: Letter.compare Letter.b Letter.a = Ordering.lt := by rfl

  inductive Modifier: Type where
    | plus: Modifier
    | natural: Modifier
    | minus: Modifier
  deriving Repr

  def Modifier.compare: Modifier → Modifier → Ordering
    | .plus, .plus | .natural, .natural | .minus, .minus => .eq
    | .plus, _ => .gt
    | .natural, .plus => .lt
    | .natural, _ => .gt
    | .minus, _ => .lt

  def Modifier.canLower: Modifier → Bool
    | .minus => false
    | _ => true

  def Modifier.lower: Modifier → Modifier
    | .plus => .natural
    | _ => .minus

  @[simp]
  theorem Modifier.eq (m: Modifier): Modifier.compare m m = Ordering.eq := by
    cases m <;> rfl

  @[simp]
  theorem Modifier.lowerMinus: Modifier.minus.lower = Modifier.minus := by rfl

  @[simp]
  theorem Modifier.lowerNonMinus (m: Modifier) (h: Modifier.compare Modifier.minus m = Ordering.lt): m.lower.compare m = Ordering.lt := by
    cases m with
      | plus => rfl
      | natural => rfl
      | minus =>
        rw [←h]
        rfl

  example: Modifier.compare Modifier.natural Modifier.natural = Ordering.eq := by rfl
  example: Modifier.compare Modifier.plus Modifier.natural = Ordering.gt := by rfl
  example: Modifier.compare Modifier.minus Modifier.natural = Ordering.lt := by rfl

  structure Grade: Type where
    letter: Letter
    modifier: Modifier
  deriving Repr

  def Grade.compare (g₁ g₂: Grade): Ordering :=
    match Letter.compare g₁.letter g₂.letter with
      | .eq => Modifier.compare g₁.modifier g₂.modifier
      | ord => ord

  def Grade.lower (g: Grade): Grade :=
    if g.modifier.canLower
    then ⟨g.letter, g.modifier.lower⟩
    else
      if g.letter.canLower
      then ⟨g.letter.lower, Modifier.plus⟩
      else g

  def Grade.late (g: Grade) (days: Nat): Grade :=
    if days < 9 then g
    else if days < 17 then g.lower
    else if days < 21 then g.lower.lower
    else g.lower.lower.lower

  @[simp]
  theorem Grade.eq (l: Letter) (m: Modifier): Grade.compare (⟨l, m⟩: Grade) ⟨l, m⟩ = Ordering.eq := by
    cases m <;> cases l <;> rfl

  def aPlus: Grade := ⟨.a, .plus⟩
  def aNatural: Grade := ⟨.a, .natural⟩
  def aMinus: Grade := ⟨.a, .minus⟩
  def bPlus: Grade := ⟨.b, .plus⟩
  def bNatural: Grade := ⟨.b, .natural⟩
  def bMinus: Grade := ⟨.b, .minus⟩
  def cPlus: Grade := ⟨.c, .plus⟩
  def cNatural: Grade := ⟨.c, .natural⟩
  def cMinus: Grade := ⟨.c, .minus⟩
  def fPlus: Grade := ⟨.f, .plus⟩
  def fNatural: Grade := ⟨.f, .natural⟩
  def fMinus: Grade := ⟨.f, .minus⟩

  example: Grade.compare aMinus bPlus = Ordering.gt := by rfl
  example: Grade.compare aMinus aPlus = Ordering.lt := by rfl
  example: Grade.compare fPlus fPlus = Ordering.eq := by rfl
  example: Grade.compare bMinus cPlus = Ordering.gt := by rfl

  example: aPlus.lower = aNatural := by rfl
  example: aNatural.lower = aMinus := by rfl
  example: aMinus.lower = bPlus := by rfl
  example: bPlus.lower = bNatural := by rfl
  example: fNatural.lower = fMinus := by rfl
  example: fMinus.lower = fMinus := by rfl

  example: bMinus.lower.lower = cNatural := by rfl
  example: bMinus.lower.lower.lower = cMinus := by rfl

  @[simp]
  theorem Grade.lowerFMinus: fMinus.lower = fMinus := by rfl

  theorem Grade.lowers (g: Grade) (h: Grade.compare fMinus.lower g = Ordering.lt): Grade.compare g.lower g = Ordering.lt := by
    rw [Grade.lower, Modifier.lower, Letter.lower]
    rw [Grade.compare, Modifier.compare]
    cases g with
      | mk letter modifier =>
        cases modifier with
          | plus => simp
          | natural => simp
          | minus =>
            rw [Letter.compare]
            cases letter with
              | a => simp
              | b => simp
              | c => simp
              | d => simp
              | f =>
                simp
                contradiction

  theorem Grade.unfoldLate (days: Nat) (g: Grade): g.late days =
    (if days < 9 then g
     else if days < 17 then g.lower
     else if days < 21 then g.lower.lower
     else g.lower.lower.lower) := by
      intros
      rfl

  theorem Grade.noPenaltyForMostlyOnTime (days: Nat) (g: Grade) (h: days < 9): (g.late days) = g := by
    simp [Grade.unfoldLate, h]

  theorem Grade.loweredOnce (days: Nat) (g: Grade) (h₁: ¬(days < 9)) (h₂: days < 17) (_: Grade.compare fMinus g = Ordering.lt): (g.late days) = g.lower := by
    simp [Grade.unfoldLate, h₁, h₂]
end LateDays

/-
### Binary Numerals
-/

inductive Bin: Type where
  | zero: Bin
  | b₀: Bin -> Bin
  | b₁: Bin -> Bin
deriving Repr

def Bin.incr: Bin → Bin
  | .zero => .b₁ .zero
  | .b₀ b => .b₁ b
  | .b₁ b => .b₀ b.incr

def Bin.toNat: Bin → Nat
  | .zero => Nat.zero
  | .b₀ b => 2 * b.toNat
  | .b₁ b => 2 * b.toNat + 1

def one: Bin := .b₁ .zero
def two: Bin := .b₀ one
def three: Bin := .b₁ one
def four: Bin := .b₀ two

example: one.incr = two := by rfl
example: two.incr = three := by rfl
example: three.incr = four := by rfl

example: two.toNat = 2 := by rfl
example: one.incr.toNat = 1 + one.toNat := by rfl
example: one.incr.incr.toNat = 2 + one.toNat := by rfl


/- Other Stuff: FizzBuzz -/

inductive FizzBuzz: Type where
  | fizz: FizzBuzz
  | buzz: FizzBuzz
  | fizzbuzz: FizzBuzz

def FizzBuzz.fizzBuzz (n: Nat): Option FizzBuzz :=
  if n % 5 == 0 && n % 7 == 0
  then .some .fizzbuzz
  else
    if n % 5 == 0
    then .some .fizz
    else
      if n % 7 == 0
      then .some .buzz
      else .none

theorem FizzBuzz.producesFizzBuzz (n: Nat) (h₁: n % 5 == 0) (h₂: n % 7 == 0): FizzBuzz.fizzBuzz n = .some .fizzbuzz := by
  rw [FizzBuzz.fizzBuzz, h₁, h₂]
  simp

theorem FizzBuzz.producesFizz (n: Nat) (h₁: n % 5 == 0) (h₂: (n % 7 == 0) = false): FizzBuzz.fizzBuzz n = .some .fizz := by
  rw [FizzBuzz.fizzBuzz, h₁, h₂]
  simp

theorem FizzBuzz.producesBuzz (n: Nat) (h₁: (n % 5 == 0) = false) (h₂: n % 7 == 0): FizzBuzz.fizzBuzz n = .some .buzz := by
  rw [FizzBuzz.fizzBuzz, h₁, h₂]
  simp

theorem FizzBuzz.producesNone (n: Nat) (h₁: (n % 5 == 0) = false) (h₂: (n % 7 == 0) = false): FizzBuzz.fizzBuzz n = .none := by
  rw [FizzBuzz.fizzBuzz, h₁, h₂]
  simp

example: FizzBuzz.fizzBuzz 35 = .some .fizzbuzz := by rfl
example: FizzBuzz.fizzBuzz 70 = .some .fizzbuzz := by rfl

example: FizzBuzz.fizzBuzz 5 = .some .fizz := by rfl
example: FizzBuzz.fizzBuzz 10 = .some .fizz := by rfl
example: FizzBuzz.fizzBuzz 15 = .some .fizz := by rfl

example: FizzBuzz.fizzBuzz 7 = .some .buzz := by rfl
example: FizzBuzz.fizzBuzz 14 = .some .buzz := by rfl
example: FizzBuzz.fizzBuzz 21 = .some .buzz := by rfl

example: FizzBuzz.fizzBuzz 1 = .none := by rfl
example: FizzBuzz.fizzBuzz 2 = .none := by rfl
example: FizzBuzz.fizzBuzz 3 = .none := by rfl
