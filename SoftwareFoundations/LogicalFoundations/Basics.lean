/-
# Functional Programming in Lean (Coq)
-/

namespace SoftwareFoundations.LogicalFoundations.Basics
  /-
  ## Introduction
  -/

  /-
  ## Data and Functions
  -/

  /-
  ### Enumerated Types
  -/

  /-
  ### Days of the Week
  -/

  inductive Day: Type where
    | monday: Day
    | tuesday: Day
    | wednesday: Day
    | thursday: Day
    | friday: Day
    | satuday: Day
    | sunday: Day

  def Day.next_weekday: Day → Day
    | .monday => .tuesday
    | .tuesday => .wednesday
    | .wednesday => .thursday
    | .thursday => .friday
    | _ => .monday

  section
    example: Day.friday.next_weekday = .monday := rfl
    example: Day.satuday.next_weekday.next_weekday = .tuesday := rfl
  end

  /-
  ### Homework Submission Guidelines
  -/

  /-
  ### Booleans
  -/

  inductive Bool: Type where
    | true: Bool
    | false: Bool

  instance: Coe _root_.Bool Bool where
    coe: _root_.Bool → Bool
      | .true => .true
      | .false => .false

  @[reducible]
  def Bool.neg: Bool → Bool
    | .true => .false
    | .false => .true

  @[reducible]
  def Bool.and: Bool → Bool → Bool
    | .true, .true => .true
    | _, _ => .false

  @[reducible]
  def Bool.or: Bool → Bool → Bool
    | .false, .false => .false
    | _, _ => .true

  scoped infixl:35 " && " => Bool.and
  scoped infixl:30 " || " => Bool.or
  scoped notation:max "!" b:40 => Bool.neg b

  section
    example: (Bool.true || .false) = .true := rfl
    example: (Bool.false || .false) = .false := rfl
    example: (Bool.false || .true) = .true := rfl
    example: (Bool.true || .true) = .true := rfl
    example: (Bool.false || .false || .true) = .true := rfl
  end

  @[reducible]
  def Bool.nand (b₁ b₂: Bool): Bool := !(b₁ && b₂)

  section
    example: Bool.true.nand .false = .true := rfl
    example: Bool.false.nand .false = .true := rfl
    example: Bool.false.nand .true = .true := rfl
    example: Bool.true.nand .true = .false := rfl
  end

  @[reducible]
  def Bool.and3 (b₁ b₂ b₃: Bool): Bool := b₁ && b₂ && b₃

  section
    example: Bool.true.and3 .true .true = .true := rfl
    example: Bool.false.and3 .true .true = .false := rfl
    example: Bool.true.and3 .false .true = .false := rfl
    example: Bool.true.and3 .true .false = .false := rfl
  end

  /-
  ### Types
  -/

  #check Bool.true
  #check Bool.true.neg
  #check Bool.neg

  #check (Bool.true: Bool)
  #check (Bool.true.neg: Bool)
  #check (Bool.neg: Bool → Bool)

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
    | primary (p: RGB): Color

  @[reducible]
  def Color.monochrome?: Color → Bool
    | .black | .white => .true
    | _ => .false

  @[reducible]
  def Color.red?: Color → Bool
    | .primary .red => .true
    | _ => .false

  /-
  ### Namespace (Modules)
  -/

  namespace Playground
    def foo: RGB := .blue
  end Playground

  def foo: Bool := .true

  #check Playground.foo
  #check foo

  /-
  ### Tuples
  -/

  namespace TuplePlayground
    inductive Bit: Type where
      | b₁: Bit
      | b₀: Bit

    structure Nybble: Type where
      b₀: Bit
      b₁: Bit
      b₂: Bit
      b₃: Bit

    @[reducible]
    def Nybble.zero?: Nybble → Bool
      | ⟨.b₀, .b₀, .b₀, .b₀⟩ => .true
      | _ => .false

    section
      #check (⟨.b₁, .b₀, .b₁, .b₀⟩: Nybble)

      example: (⟨.b₁, .b₀, .b₁, .b₀⟩: Nybble).zero? = .false := rfl
      example: (⟨.b₀, .b₀, .b₀, .b₀⟩: Nybble).zero? = .true := rfl
    end
  end TuplePlayground

  /-
  ### Numbers
  -/

  namespace NatPlayground
    inductive Nat: Type where
      | zero: Nat
      | succ (n: Nat): Nat

    inductive StrangeNat: Type where
      | foo: StrangeNat
      | bar (s: StrangeNat): StrangeNat

    @[reducible]
    def Nat.pred: Nat → Nat
      | .zero => .zero
      | .succ n => n
  end NatPlayground

  #check Nat.zero.succ.succ.succ.succ

  @[reducible]
  def _root_.Nat.minusTwo: Nat → Nat
    | .zero | .succ .zero => .zero
    | .succ (.succ n) => n

  section
    example: (4).minusTwo = 2 := rfl

    #check Nat.succ
    #check Nat.pred
    #check Nat.minusTwo
  end

  @[reducible]
  def _root_.Nat.even?: Nat → Bool
    | .zero => .true
    | .succ .zero => .false
    | .succ (.succ n) => n.even?

  @[reducible]
  def _root_.Nat.odd? (n: Nat): Bool := n.even?.neg

  section
    example: (1).odd? = .true := rfl
    example: (4).odd? = .false := rfl
  end

  namespace NatPlayground2
    def Nat.plus: Nat → Nat → Nat
      | .zero, n₂ => n₂
      | .succ n₁, n₂ => plus n₁ n₂.succ

    def Nat.mult: Nat → Nat → Nat
      | .zero, _ => 0
      | .succ .zero, n₂ => n₂
      | .succ n₁, n₂ => Nat.plus (Nat.mult n₁ n₂) n₂

    def Nat.minus: Nat → Nat → Nat
      | .zero, _ => 0
      | n, .zero => n
      | .succ n₁, .succ n₂ => Nat.minus n₁ n₂

    scoped instance: Add Nat where
      add := Nat.plus
    scoped instance: Sub Nat where
      sub := Nat.minus
    scoped instance: Mul Nat where
      mul := Nat.mult

    section
      example: 3 + 2 = 5 := rfl
      example: 2 - 9 = 0 := rfl
      example: 9 - 2 = 7 := rfl
      example: 3 * 3 = 9 := rfl
    end
  end NatPlayground2

  def _root_.Nat.exp: Nat → Nat → Nat
    | _, .zero => 1
    | n₁, .succ n₂ => n₁ * (n₁.exp n₂)

  def _root_.Nat.factorial: Nat → Nat
    | 0 => 0
    | 1 => 1
    | .succ n => (n + 1) * n.factorial

  section
    example: (3).factorial = 6 := rfl
    example: (5).factorial = 10 * 12 := rfl
  end

  #check _root_.Nat.beq
  #check _root_.Nat.ble
  #check _root_.Nat.blt

  def _root_.Nat.eqb: Nat → Nat → Bool
    | .zero, .zero => .true
    | .succ n₁, .succ n₂ => n₁.eqb n₂
    | _, _ => false

  def _root_.Nat.leb: Nat → Nat → Bool
    | .zero, _ => .true
    | .succ _, .zero => .false
    | .succ n₁, .succ n₂ => n₁.leb n₂

  def _root_.Nat.ltb (n₁ n₂: Nat): Bool := (n₁.leb n₂) && !(n₁.eqb n₂)

  section
    example: (2).leb 2 = .true := rfl
    example: (2).leb 4 = .true := rfl
    example: (4).leb 2 = .false := rfl

    example: (2).ltb 2 = .false := rfl
    example: (2).ltb 4 = .true := rfl
    example: (4).ltb 2 = .false := rfl
  end

  /-
  ## Proof By Simplification

  Note: Becase of subtle implementation difference in Lean's `Nat.add` (vs
  Coq's `plus`), the order of the operands in these theorems is reversed from
  the book.

  In the next chapter, `Induction`, the operands will be reversed as well for
  the same reason.
  -/

  namespace Term
    theorem Nat.add_zero (n: Nat): n + 0 = n := rfl
    theorem Nat.add_one_eq_succ (n: Nat): n + 1 = n.succ := rfl
    theorem Nat.mul_zero (n: Nat): n * 0 = 0 := rfl
  end Term

  namespace Tactic
    @[scoped simp]
    theorem Nat.add_zero (n: Nat): n + 0 = n := by rfl

    @[scoped simp]
    theorem Nat.add_one_eq_succ (n: Nat): n + 1 = n.succ := by rfl

    @[scoped simp]
    theorem Nat.mul_zero (n: Nat): n * 0 = 0 := by rfl
  end Tactic

  namespace Blended
    @[scoped simp]
    theorem Nat.add_zero (n: Nat): n + 0 = n := rfl

    @[scoped simp]
    theorem Nat.add_one_eq_succ (n: Nat): n + 1 = n.succ := rfl

    @[scoped simp]
    theorem Nat.mul_zero (n: Nat): n * 0 = 0 := rfl
  end Blended

  /-
  ## Proof By Rewriting

  Note: Subtle implementation difference in Lean Nat.add (vs Coq) makes the
  Nat.mul_one impossible at this point using only the theorems proven so far.
  -/

  namespace Term
    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁ + n₁ = n₂ + n₂ :=
      calc n₁ + n₁
        _ = n₂ + n₂ := congr (congrArg Nat.add h) h

    example {n₁ n₂ n₃: Nat} (h₁: n₁ = n₂) (h₂: n₂ = n₃): n₁ + n₂ = n₂ + n₃ :=
      calc n₁ + n₂
        _ = n₂ + n₃ := congr (congrArg Nat.add h₁) h₂

    theorem Nat.mul_zero_add_mul_zero (n₁ n₂: Nat): (n₁ * 0) + (n₂ * 0) = 0 :=
      calc (n₁ * 0) + (n₂ * 0)
        _ = 0 + 0 := congr (congrArg Nat.add (Nat.mul_zero n₁)) (Nat.mul_zero n₂)

    theorem Nat.mul_one (n: Nat): n * 1 = n :=
      calc n * 1
        _ = n := _root_.Nat.mul_one n
  end Term

  namespace Tactic
    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁ + n₁ = n₂ + n₂ := by
      rw [h]

    example {n₁ n₂ n₃: Nat} (h₁: n₁ = n₂) (h₂: n₂ = n₃): n₁ + n₂ = n₂ + n₃ := by
      rw [h₁, h₂]

    @[scoped simp]
    theorem Nat.mul_zero_add_mul_zero (n₁ n₂: Nat): (n₁ * 0) + (n₂ * 0) = 0 := by
      rw [Nat.mul_zero, Nat.mul_zero]

    theorem Nat.mul_one (n: Nat): n * 1 = n := by
      simp
  end Tactic

  namespace Blended
    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁ + n₁ = n₂ + n₂ :=
      calc n₁ + n₁
        _ = n₂ + n₂ := by rw [h]

    example {n₁ n₂ n₃: Nat} (h₁: n₁ = n₂) (h₂: n₂ = n₃): n₁ + n₂ = n₂ + n₃ :=
      calc n₁ + n₂
        _ = n₂ + n₃ := by rw [h₁, h₂]

    @[scoped simp]
    theorem Nat.mul_zero_add_mul_zero (n₁ n₂: Nat): (n₁ * 0) + (n₂ * 0) = 0 :=
      calc (n₁ * 0) + (n₂ * 0)
        _ = 0 + 0 := by rw [Nat.mul_zero, Nat.mul_zero]

    @[scoped simp]
    theorem Nat.mul_one (n: Nat): n * 1 = n := by
      calc n * 1
        _ = n := by simp
  end Blended

  /-
  ## Proof By Case Analysis
  -/

  namespace Term
    theorem Nat.succ_neqb_zero: ∀ n: Nat, (n + 1).eqb 0 = .false
      | .zero => rfl
      | .succ _ => rfl

    theorem Bool.neg_involute: ∀ b: Bool, b.neg.neg = b
      | .true => rfl
      | .false => rfl

    theorem Bool.and_comm: ∀ b₁ b₂: Bool, (b₁ && b₂) = (b₂ && b₁)
      | .true, .true => rfl
      | .true, .false => rfl
      | .false, .true => rfl
      | .false, .false => rfl

    theorem Bool.and_exchange: ∀ b₁ b₂ b₃: Bool, ((b₁ && b₂) && b₃) = ((b₁ && b₃) && b₂)
      | .true, .true, .true => rfl
      | .true, .true, .false => rfl
      | .true, .false, .true => rfl
      | .true, .false, .false => rfl
      | .false, .true, .true => rfl
      | .false, .true, .false => rfl
      | .false, .false, .true => rfl
      | .false, .false, .false => rfl

    theorem Bool.and_true: ∀ b₁ b₂: Bool, (b₁ && b₂) = .true → b₂ = .true
      | _, .true, _ => rfl
      | .true, .false, h =>
        have h :=
          calc Bool.true
            _ = (Bool.true && .false) := Eq.symm h
            _ = Bool.false            := rfl
        Eq.symm h

    theorem Nat.zero_neqb_succ: ∀ n: Nat, (0).eqb (n + 1) = .false
      | .zero => rfl
      | .succ _ => rfl
  end Term

  namespace Tactic
    theorem Nat.succ_neqb_zero: ∀ n: Nat, (n + 1).eqb 0 = .false := by
      intro
      | .zero => rfl
      | .succ _ => rfl

    @[scoped simp]
    theorem Bool.neg_involute: ∀ b: Bool, b.neg.neg = b := by
      intro
      | .true => rfl
      | .false => rfl

    theorem Bool.and_comm: ∀ b₁ b₂: Bool, (b₁ && b₂) = (b₂ && b₁) := by
      intro
      | .true, .true => rfl
      | .true, .false => rfl
      | .false, .true => rfl
      | .false, .false => rfl

    theorem Bool.and_exchange: ∀ b₁ b₂ b₃: Bool, ((b₁ && b₂) && b₃) = ((b₁ && b₃) && b₂) := by
      intro
      | .true, .true, .true => rfl
      | .true, .true, .false => rfl
      | .true, .false, .true => rfl
      | .true, .false, .false => rfl
      | .false, .true, .true => rfl
      | .false, .true, .false => rfl
      | .false, .false, .true => rfl
      | .false, .false, .false => rfl

    theorem Bool.and_true: ∀ b₁ b₂: Bool, (b₁ && b₂) = .true → b₂ = .true := by
      intro
      | _, .true, _ => rfl
      | .true, .false, _ => contradiction

    theorem Nat.zero_neqb_succ: ∀ n: Nat, (0).eqb (n + 1) = .false := by
      intro
      | .zero => rfl
      | .succ _ => rfl
  end Tactic

  namespace Blended
    theorem Nat.succ_neqb_zero: ∀ n: Nat, (n + 1).eqb 0 = .false
      | .zero => by rfl
      | .succ _ => by rfl

    @[scoped simp]
    theorem Bool.neg_involute: ∀ b: Bool, b.neg.neg = b
      | .true => by rfl
      | .false => by rfl

    theorem Bool.and_comm: ∀ b₁ b₂: Bool, (b₁ && b₂) = (b₂ && b₁)
      | .true, .true => by rfl
      | .true, .false => by rfl
      | .false, .true => by rfl
      | .false, .false => by rfl

    theorem Bool.and_exchange: ∀ b₁ b₂ b₃: Bool, ((b₁ && b₂) && b₃) = ((b₁ && b₃) && b₂)
      | .true, .true, .true => by rfl
      | .true, .true, .false => by rfl
      | .true, .false, .true => by rfl
      | .true, .false, .false => by rfl
      | .false, .true, .true => by rfl
      | .false, .true, .false => by rfl
      | .false, .false, .true => by rfl
      | .false, .false, .false => by rfl

    theorem Bool.and_true: ∀ b₁ b₂: Bool, (b₁ && b₂) = .true → b₂ = .true
      | _, .true, _ => by rfl
      | .true, .false, h => by rw [← h]

    theorem Nat.zero_neqb_succ: ∀ n: Nat, (0).eqb (n + 1) = .false
      | .zero => by rfl
      | .succ _ => by rfl
  end Blended

  /-
  ### More on Notation (Optional)
  -/

  /-
  ### Fixpoints and Structural Recursion
  -/

  /-
  ## More Exercises
  -/

  /-
  ### Warmups
  -/

  namespace Term
    example {b: Bool} (f: Bool → Bool) (h: (b: Bool) → f b = b): f (f b) = b :=
      calc f (f b)
        _ = f b := congrArg f (h b)
        _ = b   := h b

    example {b: Bool} (f: Bool → Bool) (h: (b: Bool) → f b = b.neg): f (f b) = b :=
      calc f (f b)
        _ = f b.neg   := congrArg f (h b)
        _ = b.neg.neg := h b.neg
        _ = b         := Bool.neg_involute b

    example: ∀ b₁ b₂: Bool, (b₁ && b₂) = (b₁ || b₂) → b₁ = b₂
      | .true, .true, _ | .false, .false, _ => rfl
      | .true, .false, h =>
        calc Bool.true
          _ = (Bool.true || .false) := rfl
          _ = (Bool.true && .false) := Eq.symm h
      | .false, .true, h =>
        calc Bool.false
          _ = (Bool.false && .true) := rfl
          _ = (Bool.false || .true) := h
  end Term

  namespace Tactic
    example {b: Bool} (f: Bool → Bool) (h: (b: Bool) → f b = b): f (f b) = b := by
      rw [h, h]

    example {b: Bool} (f: Bool → Bool) (h: (b: Bool) → f b = b.neg): f (f b) = b := by
      rw [h, h, Bool.neg_involute]

    example: ∀ b₁ b₂: Bool, (b₁ && b₂) = (b₁ || b₂) → b₁ = b₂ := by
      intro
      | .true, .true, _ => rfl
      | .false, .false, _ => rfl
      | .true, .false, h =>
        calc Bool.true
          _ = (Bool.true || .false) := by rfl
          _ = (Bool.true && .false) := by rw [h]
      | .false, .true, h =>
        calc Bool.false
          _ = (Bool.false && .true) := by rfl
          _ = (Bool.false || .true) := by rw [h]
  end Tactic

  namespace Blended
    example {b: Bool} (f: Bool → Bool) (h: (b: Bool) → f b = b): f (f b) = b :=
      calc f (f b)
        _ = f b := by rw [h]
        _ = b   := by rw [h]

    example {b: Bool} (f: Bool → Bool) (h: (b: Bool) → f b = b.neg): f (f b) = b :=
      calc f (f b)
        _ = f b.neg   := by rw [h]; simp_all
        _ = b.neg.neg := by rw [h]
        _ = b         := by rw [Bool.neg_involute]

    example: ∀ b₁ b₂: Bool, (b₁ && b₂) = (b₁ || b₂) → b₁ = b₂
      | .true, .true, _ | .false, .false, _ => by rfl
      | .true, .false, h =>
        calc Bool.true
          _ = (Bool.true || .false) := by rfl
          _ = (Bool.true && .false) := by rw [h]
      | .false, .true, h =>
        calc Bool.false
          _ = (Bool.false && .true) := by rfl
          _ = (Bool.false || .true) := by rw [h]
  end Blended

  /-
  ### Course Late Policies, Formalized
  -/

  namespace LateDays
    #print Ordering

    inductive Letter: Type where
      | a: Letter
      | b: Letter
      | c: Letter
      | d: Letter
      | f: Letter
    deriving Repr

    @[reducible]
    def Letter.compare: Letter → Letter → Ordering
      | .a, .a => .eq
      | .a, _ => .gt
      | .b, .a => .lt
      | .b, .b => .eq
      | .b, _ => .gt
      | .c, .a | .c, .b => .lt
      | .c, .c => .eq
      | .c, _ => .gt
      | .d, .a | .d, .b | .d, .c => .lt
      | .d, .d => .eq
      | .d, _ => .gt
      | .f, .f => .eq
      | .f, _ => .lt

    @[reducible]
    def Letter.lower: Letter → Letter
      | .a => .b
      | .b => .c
      | .c => .d
      | _ => .f

    section
      example: Letter.b.compare .a = .lt := rfl
      example: Letter.d.compare .d = .eq := rfl
      example: Letter.b.compare .f = .gt := rfl
    end

    namespace Term
      theorem Letter.compare.eq: ∀ l: Letter, l.compare l = .eq
        | .a | .b | .c | .d | .f => rfl

      theorem Letter.lower.lowers: ∀ l: Letter, Letter.f.compare l = .lt → l.lower.compare l = .lt
        | .a, _ | .b, _ | .c, _ | .d, _ => rfl
    end Term

    namespace Tactic
      theorem Letter.compare.eq: ∀ l: Letter, l.compare l = .eq := by
        intro
        | .a | .b | .c | .d | .f => rfl

      theorem Letter.lower.lowers: ∀ l: Letter, Letter.f.compare l = .lt → l.lower.compare l = .lt := by
        intro
        | .a, _ | .b, _ | .c, _ | .d, _ => rfl
    end Tactic

    namespace Blended
      theorem Letter.compare.eq: ∀ l: Letter, l.compare l = .eq
        | .a | .b | .c | .d | .f => by rfl

      theorem Letter.lower.lowers: ∀ l: Letter, Letter.f.compare l = .lt → l.lower.compare l = .lt
        | .a, _ | .b, _ | .c, _ | .d, _ => by rfl
    end Blended

    inductive Modifier: Type where
      | plus: Modifier
      | natural: Modifier
      | minus: Modifier
    deriving Repr

    @[reducible]
    def Modifier.compare: Modifier → Modifier → Ordering
      | .plus, .plus => .eq
      | .plus, _ => .gt
      | .natural, .plus => .lt
      | .natural, .natural => .eq
      | .natural, _ => .gt
      | .minus, .minus => .eq
      | .minus, _ => .lt

    @[reducible]
    def Modifier.lower: Modifier → Modifier
      | .plus => .natural
      | _ => .minus

    structure Grade where
      letter: Letter
      modifier: Modifier
    deriving Repr

    @[reducible]
    def Grade.compare (g₁ g₂: Grade): Ordering :=
      match g₁.letter.compare g₂.letter with
        | .eq => g₁.modifier.compare g₂.modifier
        | ord => ord

    @[reducible]
    def Grade.lower: Grade → Grade
      | ⟨.f, .minus⟩ => ⟨.f, .minus⟩
      | ⟨l, .minus⟩ => ⟨l.lower, .plus⟩
      | ⟨l, m⟩ => ⟨l, m.lower⟩

    section
      def aPlus: Grade := ⟨.a, .plus⟩
      def a: Grade := ⟨.a, .natural⟩
      def aMinus: Grade := ⟨.a, .minus⟩

      def bPlus: Grade := ⟨.b, .plus⟩
      def b: Grade := ⟨.b, .natural⟩
      def bMinus: Grade := ⟨.b, .minus⟩

      def cPlus: Grade := ⟨.c, .plus⟩
      def c: Grade := ⟨.c, .natural⟩
      def cMinus: Grade := ⟨.c, .minus⟩

      def dPlus: Grade := ⟨.d, .plus⟩
      def d: Grade := ⟨.d, .natural⟩
      def dMinus: Grade := ⟨.d, .minus⟩

      def fPlus: Grade := ⟨.f, .plus⟩
      def f: Grade := ⟨.f, .natural⟩
      def fMinus: Grade := ⟨.f, .minus⟩
    end

    section
      example: aMinus.compare bPlus = .gt := rfl
      example: aMinus.compare aPlus = .lt := rfl
      example: fPlus.compare fPlus = .eq := rfl
      example: bMinus.compare cPlus = .gt := rfl

      example: aPlus.lower = a := rfl
      example: a.lower = aMinus := rfl
      example: aMinus.lower = bPlus := rfl
      example: bPlus.lower = b := rfl
      example: f.lower = fMinus := rfl
      example: bMinus.lower.lower = c := rfl
      example: bMinus.lower.lower.lower = cMinus := rfl

      example: fMinus.lower = fMinus := rfl
    end

    namespace Term
      theorem Grade.lower.lowers: ∀ g: Grade, fMinus.compare fMinus = .lt → g.lower.compare g = .lt
        | ⟨l, m⟩, _ => sorry
    end Term

    namespace Tactic
    end Tactic

    namespace Blended
    end Blended

    @[reducible]
    def Grade.late (g: Grade) (days: Nat): Grade :=
      if days < 9
      then g
      else if days < 17
           then g.lower
           else if days < 21
                then g.lower.lower
                else g.lower.lower.lower

    namespace Term
      example {g: Grade} {days: Nat} (h: days < 9): g.late days = g := sorry
      example {g: Grade} {days: Nat} (h₁: ¬ (days < 9)) (h₂: days < 17): g.late days = g.lower := sorry
    end Term

    namespace Tactic
      example {g: Grade} {days: Nat} (h: days < 9): g.late days = g := by
        unfold Grade.late
        simp [h]

      example {g: Grade} {days: Nat} (h₁: ¬ (days < 9)) (h₂: days < 17): g.late days = g.lower := by
        unfold Grade.late
        simp [h₁, h₂]

    end Tactic

    namespace Blended
      example {g: Grade} {days: Nat} (h: days < 9): g.late days = g := sorry
      example {g: Grade} {days: Nat} (h₁: ¬ (days < 9)) (h₂: days < 17): g.late days = g.lower := sorry
    end Blended
  end LateDays

  /-
  ### Binary Numerals
  -/

  inductive Bin: Type where
    | nil: Bin
    | zero (b: Bin): Bin
    | one (b: Bin): Bin

  def Bin.incr: Bin → Bin
    | .nil => .nil
    | .zero b => .one b
    | .one .nil => .zero (.one .nil)
    | .one b => .zero b.incr

  def Bin.toNat: Bin → Nat
    | .nil => 0
    | .zero b => 2 * b.toNat
    | .one b  => 1 + 2 * b.toNat

  instance: Coe Bin Nat where
    coe := Bin.toNat

  section
    example: (Bin.one .nil).incr = Bin.zero (.one .nil) := rfl
    example: (Bin.zero (.one .nil)).incr = Bin.one (.one .nil) := rfl
    example: (Bin.one (.one .nil)).incr = Bin.zero (.zero (.one .nil)) := rfl

    example: (Bin.zero (.one .nil)).toNat = 2 := rfl

    example: (Bin.one .nil).incr.toNat = 1 + (Bin.one .nil) := rfl
    example: (Bin.one .nil).incr.incr.toNat = 2 + (Bin.one .nil) := rfl
  end

  /-
  ## Testing Your Solutions
  -/
end SoftwareFoundations.LogicalFoundations.Basics
