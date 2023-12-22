/-
# Inductive Types
-/

/-
## Enumerated Types
-/

inductive Weekday: Type where
  | sunday: Weekday
  | monday: Weekday
  | tuesday: Weekday
  | wednesday: Weekday
  | thursday: Weekday
  | friday: Weekday
  | saturday: Weekday
deriving Repr

#check Weekday.sunday
#check Weekday.monday

section
  open Weekday

  #check sunday
  #check monday
end

def Weekday.numberOfDay: Weekday → Nat
  | .sunday => 1
  | .monday => 2
  | .tuesday => 3
  | .wednesday => 4
  | .thursday => 5
  | .friday => 6
  | .saturday => 7

#eval Weekday.sunday.numberOfDay
#eval Weekday.monday.numberOfDay
#eval Weekday.tuesday.numberOfDay

section
  set_option pp.all true

  #print Weekday.numberOfDay
  -- #print Weekday.numberOfDay.match_1
  #print Weekday.casesOn
  #print Weekday.rec
end

def Weekday.next: Weekday → Weekday
  | .sunday => .monday
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | .friday => .saturday
  | .saturday => .sunday

def Weekday.previous: Weekday → Weekday
  | .sunday => .saturday
  | .monday => .sunday
  | .tuesday => .monday
  | .wednesday => .tuesday
  | .thursday => .wednesday
  | .friday => .thursday
  | .saturday => .friday

#eval Weekday.tuesday.next.next
#eval Weekday.tuesday.previous.next

example (w: Weekday): w.previous.next = w := by
  cases w <;> rfl

example (w: Weekday): w.previous.next = w :=
  match w with
    | .sunday => rfl
    | .monday=> rfl
    | .tuesday => rfl
    | .wednesday => rfl
    | .thursday => rfl
    | .friday => rfl
    | .saturday => rfl

example (w: Weekday): w.previous.next = w :=
  match w with
    | .sunday | .monday | .tuesday | .wednesday | .thursday | .friday | .saturday => rfl

inductive 𝔹: Type where
  | true: 𝔹
  | false: 𝔹

def 𝔹.band: 𝔹 → 𝔹 → 𝔹
  | .true, .true => .true
  | _, _ => .false

/-
## Constructors with Arguments
-/

namespace Hidden
  inductive Prod (α: Type) (β: Type): Type where
    | mk: α → β → Prod α β

  inductive Sum (α: Type) (β: Type): Type where
    | inl: α → Sum α β
    | inr: β → Sum α β

  def Prod.fst: Prod α β → α
    | mk a _ => a
  def Prod.snd: Prod α β → β
    | mk _ b => b

  def Prod.example (p: Prod Bool Nat): Nat :=
    Prod.casesOn (motive := fun _ => Nat) p mk
    where
      mk (b: Bool) (n: Nat): Nat := cond b (2 * n) (2 * n + 1)

  def Sum.example (s: Sum Nat Nat): Nat :=
    Sum.casesOn (motive := fun _ => Nat) s inl inr
    where
      inl (n: Nat): Nat := 2 * n
      inr (n: Nat): Nat := 2 * n + 1

  #eval (Sum.inl 3).example
  #eval (Sum.inr 3).example

  structure ProdStruct (α: Type) (β: Type): Type where
    fst: α
    snd: β

  #check (⟨1, true⟩: ProdStruct Nat Bool)

  structure Color: Type where
    red: Nat
    green: Nat
    blue: Nat
  deriving Repr

  def yellow: Color := Color.mk 255 255 0
  #eval yellow.red

  structure Semigroup where
    carrier: Type u
    mul: carrier → carrier → carrier
    mulAssoc: ∀ (a b c: carrier), mul (mul a b) c = mul a (mul b c)

  inductive Sigma {α: Type u} (β: α → Type v) where
    | mk: (a: α) → β a → Sigma β

  inductive Option (α: Type): Type where
    | some: α → Option α
    | none: Option α

  inductive Inhabited (α: Type): Type where
    | mk: α → Inhabited α
end Hidden

/-
## Inductively Defined Propositions
-/

namespace Hidden
  inductive False: Prop

  inductive True: Prop where
    | intro: True

  inductive And (a b: Prop): Prop where
    | intro: a → b → And a b

  inductive Or (a b: Prop): Prop where
    | inl: a → Or a b
    | inr: b → Or a b

  inductive Exists {α: Sort u} (p: α → Prop): Prop where
    | mk (w: α): p w → Exists p

  inductive Subtype {α: Sort u} (p: α → Prop) where
    | mk (w: α): p w → Subtype p
end Hidden

/-
## Defining the Natural Numbers
-/

namespace Hidden
  inductive Nat: Type where
    | zero: Nat
    | succ: Nat → Nat
  deriving Repr

  #check @Nat.rec
  #check @Nat.recOn

  def Nat.add: Nat → Nat → Nat
    | n, .zero => n
    | n₁, .succ n₂ => .succ (n₁.add n₂)

  #eval (Nat.zero.succ.succ.add Nat.zero.succ)

  instance: Add Nat where
    add := Nat.add

  #eval (Nat.zero.succ.succ + Nat.zero.succ)

  theorem Nat.addZero (n: Nat): n + Nat.zero = n := rfl
  theorem Nat.addSucc (n₁ n₂: Nat): n₁ + n₂.succ = Nat.succ (n₁ + n₂) := rfl
end Hidden

#print Nat.add
#check Nat.recOn

theorem Nat.zeroAdd (n: Nat): 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n base induct
  where
    base := rfl
    induct (n: Nat) (h: 0 + n = n) :=
      calc 0 + succ n
        _ = succ (0 + n) := rfl
        _ = succ n       := by rw [h]

example: 0 + n = n :=
  Nat.recOn
    (motive := fun x => 0 + x = x)
    n
    rfl
    (by simp_all)

theorem Nat.addAssoc (n₁ n₂ n₃: Nat): n₁ + n₂ + n₃ = n₁ + (n₂ + n₃) :=
  Nat.recOn (motive := fun k => n₁ + n₂ + k = n₁ + (n₂ + k)) n₃
    base induct
  where
    base := rfl
    induct (k: Nat) (h: n₁ + n₂ + k = n₁ + (n₂ + k)) :=
      calc n₁ + n₂ + k.succ
        _ = succ (n₁ + n₂ + k)   := rfl
        _ = succ (n₁ + (n₂ + k)) := by rw [h]
        _ = n₁ + (n₂ + k).succ   := rfl
        _ = n₁ + (n₂ + k.succ)   := rfl

example (n₁ n₂ n₃: Nat): n₁ + n₂ + n₃ = n₁ + (n₂ + n₃) :=
  Nat.recOn
    (motive := fun k => n₁ + n₂ + k = n₁ + (n₂ + k))
    n₃
    rfl
    (by simp_all [Nat.add_succ])

theorem Nat.succAdd (n₁ n₂: Nat): n₁.succ + n₂ = (n₁ + n₂).succ :=
  Nat.recOn
    (motive := fun k => n₁.succ + k = (n₁ + k).succ)
    n₂
    base
    induct
  where
    base := rfl
    induct (k: Nat) (h: n₁.succ + k = (n₁ + k).succ) :=
      calc n₁.succ + k.succ
        _ = (n₁.succ + k).succ := rfl
        _ = (n₁ + k).succ.succ := by rw [h]
        _ = (n₁ + k.succ).succ := rfl

theorem Nat.addComm (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ :=
  Nat.recOn
    (motive := fun k => n₁ + k = k + n₁)
    n₂
    base
    induct
  where
    base := by simp [Nat.add_zero, Nat.zero_add]
    induct (k: Nat) (h: n₁ + k = k + n₁) :=
      calc n₁ + k.succ
        _ = (n₁ + k).succ := rfl
        _ = (k + n₁).succ := by rw [h]
        _ = k.succ + n₁   := Eq.symm (Nat.succAdd k n₁)

namespace Shortened
  theorem Nat.succAdd (n₁ n₂: Nat): n₁.succ + n₂ = (n₁ + n₂).succ :=
    Nat.recOn
      (motive := fun k => n₁.succ + k = (n₁ + k).succ)
      n₂
      rfl
      (by intro; simp_all [Nat.add_succ])

  theorem Nat.addComm (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ :=
    Nat.recOn
      (motive := fun k => n₁ + k = k + n₁)
      n₂
      (by simp)
      (by intro; simp_all [Nat.add_succ, Nat.succ_add])
end Shortened

/-
## Other Recursive Data Types
-/

namespace Hidden
  inductive List (α: Type): Type :=
    | nil: List α
    | cons: α → List α → List α

  def List.append: List α → List α → List α
    | .nil, l => l
    | .cons hd tl, l => .cons hd (append tl l)

  instance: Append (List α) where
    append := List.append

  theorem List.nilAppend (l: List α): .nil ++ l = l := rfl
  theorem List.consAppend (x: α) (l₁ l₂: List α): (.cons x l₁) ++ l₂ = .cons x (l₁ ++ l₂) := rfl

  theorem List.appendNil (l: List α): l ++ .nil = l :=
    List.recOn
      (motive := fun k => k ++ .nil = k)
      l
      base
      recur
    where
      base := rfl
      recur (hd: α) (tl: List α) (h: tl ++ .nil = tl) :=
        calc List.cons hd tl ++ .nil
          _ = List.cons hd (tl ++ .nil) := List.consAppend hd tl .nil
          _ = List.cons hd tl := by rw [h]

  theorem List.appendAssoc (l₁ l₂ l₃: List α): (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) :=
    List.recOn
      (motive := fun k => (k ++ l₂) ++ l₃ = k ++ (l₂ ++ l₃))
      l₁
      base
      recur
    where
      base :=
        calc (.nil ++ l₂) ++ l₃
          _ = l₂ ++ l₃ := by rw [List.nilAppend]
          _ = .nil ++ (l₂ ++ l₃) := by rw [List.nilAppend]

      recur (hd: α) (tl: List α) (h: (tl ++ l₂) ++ l₃ = tl ++ (l₂ ++ l₃)) :=
        calc (.cons hd tl ++ l₂) ++ l₃
          _ = .cons hd (tl ++ l₂) ++ l₃   := by rw [List.consAppend]
          _ = .cons hd ((tl ++ l₂) ++ l₃) := by rw [List.consAppend]
          _ = .cons hd (tl ++ (l₂ ++ l₃)) := by rw [h]
          _ = .cons hd tl ++ (l₂ ++ l₃)   := by rw [← List.consAppend]

  example (l: List α): l ++ .nil = l :=
    List.recOn
      (motive := fun k => k ++ .nil = k)
      l
      (by rfl)
      recur
    where
      recur (hd: α) (tl: List α) (h: tl ++ .nil = tl) := by
        simp [List.consAppend, h]

  example (l₁ l₂ l₃: List α): (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) :=
    List.recOn
      (motive := fun k => (k ++ l₂) ++ l₃ = k ++ (l₂ ++ l₃))
      l₁
      (by simp [List.nilAppend])
      recur
    where
      recur (hd: α) (tl: List α) (h: (tl ++ l₂) ++ l₃ = tl ++ (l₂ ++ l₃)) := by
        simp [List.consAppend, h]

  example (l: List α): l ++ .nil = l := by
    induction l with
      | nil => rfl
      | cons _ _ ih => simp [List.consAppend, ih]

  example (l₁ l₂ l₃: List α): (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
    induction l₁ with
      | nil => simp [List.nilAppend]
      | cons _ _ ih => simp [List.consAppend, ih]

  def List.length: List α → _root_.Nat
    | .nil => 0
    | .cons _ tl => 1 + tl.length

  theorem List.appendLength (l₁ l₂: List α): (l₁ ++ l₂).length = l₁.length + l₂.length :=
    List.recOn (motive := fun k => (k ++ l₂).length = k.length + l₂.length)
      l₁
      base
      recur
    where
      base :=
        calc (.nil ++ l₂).length
          _ = l₂.length := by rw [List.nilAppend]
          _ = 0 + l₂.length := by rw [Nat.zeroAdd]

      recur (hd: α) (tl: List α) (h: ((tl ++ l₂).length = tl.length + l₂.length)) :=
        calc (.cons hd tl ++ l₂).length
          _ = (List.cons hd (tl ++ l₂)).length := by rw [List.consAppend]
          _ = 1 + (tl ++ l₂).length := by rw [List.length]
          _ = 1 + (tl.length + l₂.length) := by rw [h]
          _ = (1 + tl.length) + l₂.length := Eq.symm (Nat.addAssoc 1 tl.length l₂.length)
          _ = (List.cons hd tl).length + l₂.length := rfl

  inductive BinaryTree: Type where
    | leaf: BinaryTree
    | node: BinaryTree → BinaryTree → BinaryTree

  inductive CountablyBranchingTree: Type where
    | leaf: CountablyBranchingTree
    | sup: (Nat → CountablyBranchingTree) → CountablyBranchingTree

  def CountablyBranchingTree.succ (t: CountablyBranchingTree): CountablyBranchingTree :=
    .sup (fun _ => t)

  def Nat.toCountablyBranchingTree: Nat → CountablyBranchingTree
    | .zero => .leaf
    | .succ n => n.toCountablyBranchingTree.succ

  def omega: CountablyBranchingTree := .sup Nat.toCountablyBranchingTree
end Hidden

/-
## Tactics for Inductive Types
-/

example (p: Nat → Prop) (hz: p 0) (hs: ∀ n: Nat, p (Nat.succ n)): ∀ n: Nat, p n := by
  intro
    | .zero => exact hz
    | .succ n => apply hs

example (n: Nat) (h: n ≠ 0): n.pred.succ = n := by
  cases n with
    | zero => apply absurd rfl h
    | succ n => rfl

def tacticsExampleFun (n: Nat): Nat := by
  cases n with
    | zero => exact 3
    | succ n => exact 7

example: tacticsExampleFun 0 = 3 := rfl
example: tacticsExampleFun 42 = 7 := rfl

def Tuple (α: Type) (n: Nat) :=
  { l: List α // l.length = n }

def tacticsExampleFun2 {n: Nat} (t: Tuple α n): Nat := by
  cases n with
    | zero => exact 3
    | succ n => exact 7

def myTuple: Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example: tacticsExampleFun2 myTuple = 7 := rfl

inductive Foo: Type where
  | bar1: Nat → Nat → Foo
  | bar2: Nat → Nat → Nat → Foo

def silly (x: Foo): Nat := by
  cases x with
    | bar1 a b => exact b
    | bar2 c d e => exact e

example: Foo → Nat
  | .bar1 _ b => b
  | .bar2 _ _ e => e

def silly2 (x: Foo): Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b

example (p: Nat → Prop) (hz: p 0) (hs: ∀ n: Nat, p (.succ n)) (m k: Nat): p (m + 3 * k) := by
  cases (m + 3 * k) with
    | zero => exact hz
    | succ n => apply hs

example (p: Nat → Prop) (hz: p 0) (hs: ∀ n: Nat, p (.succ n)) (m k: Nat): p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n with
    | zero => exact hz
    | succ n => apply hs

example (p: Prop) (m n: Nat) (h₁: m < n → p) (h₂: m ≥ n → p): p := by
  cases Nat.lt_or_ge m n with
    | inl hlt => exact h₁ hlt
    | inr hge => exact h₂ hge

example (p: Prop) (m n: Nat) (h₁: m < n → p) (h₂: m ≥ n → p): p :=
  match Nat.lt_or_ge m n with
    | .inl hlt => h₁ hlt
    | .inr hge => h₂ hge

#check Nat.sub_self

example (m n: Nat): m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
    | inl hp =>
      rw [hp]
      apply Or.inl
      exact Nat.sub_self n
    | inr hnp =>
      apply Or.inr
      exact hnp

example (n: Nat): 0 + n = n := by
  induction n with
    | zero => rfl
    | succ n ih => rw [Nat.add_succ, ih]

example (n: Nat): 0 + n = n := by
  induction n <;> simp [*, Nat.add_zero, Nat.add_succ]

example (n₁ n₂: Nat): n₁.succ + n₂ = (n₁ + n₂).succ := by
  induction n₂ <;> simp [*, Nat.add_zero, Nat.add_succ]

example (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ := by
  induction n₂ <;> simp [*, Nat.add_zero, Nat.zero_add, Nat.add_succ, Nat.succ_add]

example (n₁ n₂ n₃: Nat): (n₁ + n₂) + n₃ = n₁ + (n₂ + n₃) := by
  induction n₃ <;> simp [*, Nat.add_zero, Nat.add_succ]

#check Nat.mod.inductionOn

example (x: Nat) {y: Nat} (h: y > 0): x % y < y := by
  induction x, y using Nat.mod.inductionOn with
    | ind x y h₁ ih =>
      rw [Nat.mod_eq_sub_mod h₁.2]
      exact ih h
    | base x y h₁ =>
      have: ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
      match this with
        | .inl h₁ => exact absurd h h₁
        | .inr h₁ =>
          have hgt: y > x := Nat.gt_of_not_le h₁
          rw [←Nat.mod_eq_of_lt hgt] at hgt
          assumption

example: p ∨ q → q ∨ p := by
  intro
    | .inl _ =>
      apply Or.inr
      assumption
    | .inr _ =>
      apply Or.inl
      assumption

example: s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example: (fun (x y: Nat × Nat) => x.1 + y.2) = (fun (x z: Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (_, d)
  show a + d = d + a
  rw [Nat.add_comm]

example (n₁ n₂ n₃: Nat) (h: n₁.succ.succ = n₂.succ.succ): n₂ + n₃ = n₁ + n₃ := by
  injection h with h₁
  injection h₁ with h₂
  rw [h₂]

example (n₁ n₂: Nat) (h: n₁.succ = 0): n = n + 7 := by
  injection h

example (n₁ n₂: Nat) (h: n₁.succ = 0): n = n + 7 := by
  contradiction

example (h: 7 = 4): False := by
  contradiction

/-
## Inductive Families
-/

inductive Vector (α: Type): Nat → Type where
  | nil: Vector α 0
  | cons: α → {n: Nat} → Vector α n → Vector α (n + 1)

namespace Hidden
  inductive Eq {α: Sort u} (a: α): α → Prop where
    | refl: Eq a a
end Hidden

universe u v
#check (@Eq.rec: {α: Sort u} → {a: α} → {motive: (x: α) → a = x → Sort v} → motive a rfl → {b: α} → (h: a = b) → motive b h)

example {α: Type u} {a b: α} {p: α → Prop} (h₁: Eq a b) (h₂: p a): p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁

theorem subst {α: Type u} {a b: α} {p: α → Prop} (h₁: Eq a b) (h₂: p a): p b :=
  match h₁ with
    | Eq.refl _ => h₂

section
  set_option pp.all true
  #print subst
  #print subst.match_1
  #print Eq.casesOn
end

example {α: Type u} {a b: α} (h: Eq a b): Eq b a :=
  match h with
    | rfl => rfl

example {α: Type u} {a b c: α} (h₁: Eq a b) (h₂: Eq b c): Eq a c :=
  match h₁ with
    | rfl =>
      match h₂ with
        | rfl => rfl

example {α: Type u} {a b: α} (f: α → β) (h: Eq a b): Eq (f a) (f b) :=
  match h with
    | rfl => rfl

/-
## Axiomatic Details
-/

/-
## Mutual and Nested Inductive Types
-/

mutual
  inductive Even: Nat → Prop where
    | zero: Even 0
    | succ: (n: Nat) → Odd n → Even (n + 1)
  inductive Odd: Nat → Prop where
    | succ: (n: Nat) → Even n → Odd (n + 1)
end

mutual
  inductive Tree (α: Type u) where
    | node: α → TreeList α → Tree α
  inductive TreeList (α: Type u) where
    | nil: TreeList α
    | cons: Tree α → TreeList α → TreeList α
end

inductive SimplerTree (α: Type u) where
  | mk: α → List (SimplerTree α) → SimplerTree α


/-
## Exercies
-/

section ExerciseOne
end ExerciseOne

section ExerciseTwo
end ExerciseTwo

section ExerciseThree
end ExerciseThree

section ExerciseFour
end ExerciseFour
