/-
# Induction Principles
-/


/-
## Basics
-/

#check Nat.recOn

example (n: Nat): n * 0 = 0 := by
  apply Nat.recOn (motive := fun n => n * 0 = 0)
  · rfl
  · simp

example (n: Nat): n * 0 = 0 :=
  have zero: 0 * 0 = 0 := Nat.zero_mul 0
  have succ (k: Nat) (h: k * 0 = 0): k.succ * 0 = 0 :=
    calc k.succ * 0
      _ = k * 0 := by rw [Nat.succ_mul, Nat.add_zero]
      _ = 0     := h
  Nat.recOn
    (motive := fun n => n * 0 = 0)
    n
    zero
    succ

example: ∀ n: Nat, n * 0 = 0
  | .zero => rfl
  | .succ n =>
    calc n.succ * 0
      _ = (n * 0) + 0 := Nat.succ_mul n 0
      _ = n * 0       := Nat.add_zero (n * 0)
      _ = 0           := _example n

example (n: Nat): n + 1 = n.succ := by
  apply Nat.recOn (motive := fun n => n + 1 = n.succ)
  · rfl
  · simp

example (n: Nat): n + 1 = n.succ :=
  have zero: 0 + 1 = Nat.zero.succ := rfl
  have succ (k: Nat) (h: k + 1 = k.succ): k.succ + 1 = k.succ.succ :=
    calc k.succ + 1
      _ = (k + 1).succ := by rw [Nat.succ_add]
      _ = k.succ.succ  := by rw [h]
  Nat.recOn (motive := fun n => n + 1 = n.succ)
    n
    zero
    succ

example: ∀ n: Nat, n + 1 = n.succ
  | .zero => rfl
  | .succ n =>
    calc n.succ + 1
      _ = (n + 1).succ := Nat.succ_add n 1
      _ = n.succ.succ  := congrArg Nat.succ (_example n)

inductive Time: Type where
  | day: Time
  | night: Time

#check Time.recOn

namespace Duplicated
  inductive RGB: Type where
    | red
    | green
    | blue

  -- RGB.recOn.{u}: ({motive: RGB → Sort u} (t: RGB) (red: motive RGB.red) (green: motive RGB.green) (blue: motive RGB.blue): motive t)
end Duplicated

inductive NatList: Type where
  | nil: NatList
  | cons (hd: Nat) (tl: NatList): NatList

#check NatList.recOn

inductive ListNat: Type where
  | nil: ListNat
  | cons (tl: ListNat) (hd: Nat): ListNat

#check ListNat.recOn

inductive BoolTree: Type where
  | empty: BoolTree
  | leaf (b: Bool): BoolTree
  | branch (b: Bool) (l r: BoolTree): BoolTree

-- BoolTree.recOn.{u} ({motive: BoolTree → Sort u} (t: BoolTree) (empty: motive BoolTree.empty) (leaf: (b: Bool) → motive (BoolTree.leaf b)) (branch: (b: Bool) → (l r: BoolTree) → motive l → motive r → (BoolTree.branch b l r)): motive t))
#check BoolTree.recOn

def BoolTreeRecType: Prop := ∀ {motive: BoolTree → Prop}, ∀ t: BoolTree, (empty: motive BoolTree.empty) → (leaf: (b: Bool) → motive (BoolTree.leaf b)) → (branch: (b: Bool) → (l r: BoolTree) → motive l → motive r → motive (BoolTree.branch b l r)) → motive t
example: BoolTreeRecType := BoolTree.recOn

inductive Toy: Type where
  | con1 (b: Bool): Toy
  | con2 (n: Nat) (t: Toy): Toy

def ToyRecType: Prop := ∀ {motive: Toy → Prop}, ∀ t: Toy, (con1: (b: Bool) -> motive (Toy.con1 b)) → (con2: (n: Nat) → (t: Toy) → motive t → motive (Toy.con2 n t)) → motive t
example: ToyRecType := Toy.recOn

/-
## Polymorphism
-/

#check List.recOn

inductive MyTree (α: Type): Type where
  | leaf (x: α): MyTree α
  | node (l r: MyTree α): MyTree α

def MyTreeRecType: Prop := ∀ {α: Type}, ∀ {motive: MyTree α → Prop}, ∀ t: MyTree α, (leaf: (x: α) → motive (MyTree.leaf x)) → (node: (l r: MyTree α) → motive l → motive r → motive (MyTree.node l r)) → motive t
example: MyTreeRecType := MyTree.recOn

inductive MyType (α: Type): Type where
  | constr1 (x: α): MyType α
  | constr2 (n: Nat): MyType α
  | constr3 (m: MyType α) (n: Nat): MyType α

def MyTypeRecType: Prop := ∀ {α: Type}, ∀ {motive: MyType α → Prop}, ∀ t: MyType α, (constr1: (x: α) → motive (MyType.constr1 x)) → (constr2: (n: Nat) → motive (MyType.constr2 n)) → (constr3: (m: MyType α) → (n: Nat) → motive m → motive (MyType.constr3 m n)) → motive t
example: MyTypeRecType := MyType.recOn

inductive Foo (α β: Type): Type where
  | bar (x: α): Foo α β
  | baz (y: β): Foo α β
  | quux (f₁: Nat → Foo α β): Foo α β

def FooRecType: Prop := ∀ {α β: Type}, ∀ {motive: Foo α β → Prop}, ∀ t: Foo α β, (bar: (x: α) → motive (Foo.bar x)) → (baz: (y: β) → motive (Foo.baz y)) → (quux: (f₁: Nat → Foo α β) → ((n: Nat) → motive (f₁ n)) → motive (Foo.quux f₁)) → motive t
example: FooRecType := Foo.recOn

inductive Bar (α: Type): Type where
  | c₁ (l: List α) (f: Bar α): Bar α
  | c₂: Bar α

def BarRecType: Prop := ∀ {α: Type}, ∀ {motive: Bar α → Prop}, ∀ t: Bar α, (c₁: (l: List α) → (f: Bar α) → motive f → motive (Bar.c₁ l f)) → (c₂: motive Bar.c₂) → motive t
example: BarRecType := Bar.recOn

/-
## Induction Hypotheses
-/

def recOn_m0r: Nat → Prop
  | n => n * 0 = 0

example (n: Nat): recOn_m0r n := by
  apply Nat.recOn (motive := recOn_m0r)
  · rfl
  · unfold recOn_m0r
    simp

/-
## More on the `induction` Tactic
-/

example: ∀ n₁ n₂ n₃: Nat, n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃
  | .zero, n₂, n₃ =>
    calc 0 + (n₂ + n₃)
      _ = n₂ + n₃ := Nat.zero_add (n₂ + n₃)
      _ = (0 + n₂) + n₃ := congrFun (congrArg Nat.add (Eq.symm (Nat.zero_add n₂))) n₃
  | .succ n₁, n₂, n₃ =>
    calc n₁.succ + (n₂ + n₃)
      _ = (n₁ + (n₂ + n₃)).succ := Nat.succ_add n₁ (n₂ + n₃)
      _ = ((n₁ + n₂) + n₃).succ := congrArg Nat.succ (_example n₁ n₂ n₃)
      _ = (n₁ + n₂).succ + n₃   := Eq.symm (Nat.succ_add (n₁ + n₂) n₃)
      _ = (n₁.succ + n₂) + n₃   := congrFun (congrArg Nat.add (Eq.symm (Nat.succ_add n₁ n₂))) n₃

example: ∀ n₁ n₂ n₃: Nat, n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃
  | .zero, n₂, n₃ => by simp
  | .succ n₁, n₂, n₃ =>
    calc n₁.succ + (n₂ + n₃)
      _ = (n₁ + (n₂ + n₃)).succ := by rw [Nat.succ_add]
      _ = ((n₁ + n₂) + n₃).succ := by rw [_example n₁ n₂ n₃]
      _ = (n₁.succ + n₂) + n₃   := by simp only [← Nat.succ_add]

example (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃ := by
  induction n₁ with
    | zero => simp
    | succ n₁ ih =>
      rw [Nat.succ_add]
      rw [ih]
      simp only [← Nat.succ_add]

example: ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁
  | .zero, n₂ =>
    calc 0 + n₂
      _ = n₂     := Nat.zero_add n₂
      _ = n₂ + 0 := Eq.symm (Nat.add_zero n₂)
  | .succ n₁, n₂ =>
    calc n₁.succ + n₂
      _ = (n₁ + n₂).succ := Nat.succ_add n₁ n₂
      _ = (n₂ + n₁).succ := congrArg Nat.succ (_example n₁ n₂)
      _ = n₂ + n₁.succ   := Eq.symm (Nat.add_succ n₂ n₁)

example: ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁
  | .zero, n₂ => by simp
  | .succ n₁, n₂ =>
    calc n₁.succ + n₂
      _ = (n₁ + n₂).succ := by rw [Nat.succ_add]
      _ = (n₂ + n₁).succ := by rw [_example n₁ n₂]
      _ = n₂ + n₁.succ   := by rw [← Nat.add_succ]

example (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ := by
  induction n₁ with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ]
      rw [ih]

example: ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁
  | n₁, .zero =>
    calc n₁ + 0
      _ = n₁     := rfl
      _ = 0 + n₁ := Eq.symm (Nat.zero_add n₁)
  | n₁, .succ n₂ =>
    calc n₁ + n₂.succ
      _ = (n₁ + n₂).succ := Nat.add_succ n₁ n₂
      _ = (n₂ + n₁).succ := congrArg Nat.succ (_example n₁ n₂)
      _ = n₂.succ + n₁   := Eq.symm (Nat.succ_add n₂ n₁)

example: ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁
  | n₁, .zero => by simp
  | n₁, .succ n₂ =>
    calc n₁ + n₂.succ
      _ = (n₁ + n₂).succ := by rw [Nat.add_succ]
      _ = (n₂ + n₁).succ := by rw [_example n₁ n₂]
      _ = n₂.succ + n₁   := by rw [← Nat.succ_add]

example (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ := by
  induction n₂ with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ]
      rw [ih]

/-
## Induction Principles for Propositions
-/

namespace Duplicated
  inductive Even: Nat → Prop where
    | zero: Even 0
    | succSucc (n: Nat) (h: Even n): Even n.succ.succ

  #check Even.recOn

  inductive AwkwardEven: Nat → Prop where
    | zero: AwkwardEven 0
    | two: AwkwardEven 2
    | sum (n₁ n₂: Nat) (h₁: AwkwardEven n₁) (h₂: AwkwardEven n₂): AwkwardEven (n₁ + n₂)

  #check AwkwardEven.recOn

  example (n: Nat): Even n → AwkwardEven n
    | .zero => AwkwardEven.zero
    | .succSucc n h =>
      have h₁: AwkwardEven n := _example n h
      AwkwardEven.sum n 2 h₁ AwkwardEven.two

  example (n: Nat) (h: Even n): AwkwardEven n :=
    have zero: AwkwardEven 0 := AwkwardEven.zero
    have succSucc (n: Nat) (_: Even n) (h₂: AwkwardEven n): AwkwardEven n.succ.succ :=
      AwkwardEven.sum n 2 h₂ AwkwardEven.two
    Even.recOn (motive := fun n _ => AwkwardEven n)
      h
      zero
      succSucc

  example (n: Nat): Even n → AwkwardEven n := by sorry
    -- apply Even.recOn (motive := fun n h => AwkwardEven n)
    -- · apply AwkwardEven.zero
    -- · sorry

  inductive Le₁: Nat → Nat → Prop where
    | eq (n: Nat): Le₁ n n
    | succ (n₁ n₂: Nat) (h: Le₁ n₁ n₂): Le₁ n₁ n₂.succ

  inductive Le₂ (n: Nat): Nat → Prop where
    | eq: Le₂ n n
    | succ (n₂: Nat) (h: Le₂ n n₂): Le₂ n n₂.succ

  #check Le₁.recOn
  #check Le₂.recOn
end Duplicated

/-
## Another Form of Induction Principles on Propositions (Optional)
-/

-- This "alternate" induction principle is actually the one Lean generates,
-- which is different from the one the Coq generates by default.

/-
## Formal vs. Informal Proofs by Induction
-/

/- ### Induction Over an Inductively Defined Set -/
/- ### Induction Over an Inductively Defined Proposition -/

/-
## Explicit Proof Objects for Induction (Optional)
-/

#print Nat.recOn
#print Nat.rec

def buildProof (P: Nat → Prop) (zero: P 0) (succ: ∀ n: Nat, P n → P n.succ) (n: Nat): P n :=
  match n with
    | .zero => zero
    | .succ n => succ n (buildProof P zero succ n)

def Nat.rec2: ∀ {motive: Nat → Prop}, (zero: motive 0) → (one: motive 1) → (succSucc: (n: Nat) → motive n → motive n.succ.succ) → (t: Nat) → motive t :=
  fun P₀ P₁ Pss =>
    let rec loc (n: Nat) :=
      match n with
        | .zero => sorry --P₀
        | .succ .zero => sorry --P₁
        | .succ (.succ n) => sorry --Pss n (loc n)
    loc

--- TODO
