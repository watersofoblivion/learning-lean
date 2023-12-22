/-
# Induction and Recursion
-/

/-
## Pattern Matching
-/

def Nat.sub1: Nat → Nat
  | 0 => 0
  | n + 1 => n

def Nat.isZero: Nat → Bool
  | 0 => true
  | _ => false

example: (0).sub1 = 0 := rfl
example (n: Nat): n.succ.sub1 = n := rfl

example: (0).isZero = .true := rfl
example (n: Nat): n.succ.isZero = .false := rfl

example: (7).sub1 = 6 := rfl
example (n: Nat): (n + 3).isZero = false := rfl

def Prod.swap: α × β → β × α
  | ⟨a, b⟩ => ⟨b, a⟩

def foo: Nat × Nat → Nat
  | ⟨n₁, n₂⟩ => n₁ + n₂

def bar: Option Nat → Nat
  | .none => 0
  | .some n => n + 1

example (p q: Prop): p ∧ q → q ∧ p
  | And.intro hp hq => And.intro hq hp

example (p q: Prop): p ∧ q → q ∧ p
  | ⟨hp, hq⟩ => ⟨hq, hp⟩

example (p q: Prop): p ∨ q → q ∨ p
  | .inl hp => .inr hp
  | .inr hq => .inl hq

def Nat.sub2: Nat → Nat
  | 0 | 1 => 0
  | n + 2 => n

example: (0).sub2 = 0 := rfl
example: (1).sub2 = 0 := rfl
example: (x + 2).sub2 = x := rfl
example: (5).sub2 = 3 := rfl

#print Nat.sub2
#print Nat.sub2.match_1
#print Nat.casesOn

example (p q: α → Prop): (∃ x: α, p x ∨ q x) → (∃ x: α, p x) ∨ (∃ x: α, q x)
  | ⟨w, .inl hpw⟩ => .inl ⟨w, hpw⟩
  | ⟨w, .inr hqw⟩ => .inr ⟨w, hqw⟩

def foo2: Nat × Nat → Nat
  | (0, _) => 0
  | (_, 0) => 1
  | (_, _) => 2

def foo3: Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

def bar2: List Nat → List Nat → Nat
  | [], [] => 0
  | a::_, [] => a
  | [], b::_ => b
  | a::_, b::_ => a + b

def Bool.and: Bool → Bool → Bool
  | true, a => a
  | false, _ => false

def Bool.or: Bool → Bool → Bool
  | true, _ => true
  | false, b => b

def Bool.cond: Bool → α → α → α
  | true, tru, _ => tru
  | false, _, fls => fls

def List.tail1 {α: Type u}: List α → List α
  | [] => []
  | _::tl => tl

def List.tail2: {α: Type u} → List α → List α
  | _, [] => []
  | _, _::tl => tl

/-
## Wildcards and Overlapping Pattens
-/

example: foo3 0     0     = 0 := rfl
example: foo3 0     (n+1) = 0 := rfl
example: foo3 (m+1) 0     = 1 := rfl
example: foo3 (m+1) (n+1) = 2 := rfl

def f1: Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 2
  | _, _ => default

example: f1 0     0     = 1       := rfl
example: f1 0     (a+1) = 1       := rfl
example: f1 (a+1) 0     = 2       := rfl
example: f1 (a+1) (b+1) = default := rfl

def f2: Nat → Nat → Option Nat
  | 0, _ => .some 1
  | _, 0 => .some 2
  | _, _ => .none

example: f2 0     0     = some 1 := rfl
example: f2 0     (a+1) = some 1 := rfl
example: f2 (a+1) 0     = some 2 := rfl
example: f2 (a+1) (b+1) = none   := rfl

def bar3: Nat → List Nat → Bool → Nat
  | 0, _, false => 0
  | 0, b::_, _ => b
  | 0, [], true => 7
  | a + 1, [], false => a
  | a + 1, [], true => a + 1
  | a + 1, b::_, _ => a + b

def foo4: Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _ => 3

#print foo4.match_1

/-
## Structural Recursion and Induction
-/

namespace Hidden
  def add: Nat → Nat → Nat
    | n₁, .zero => n₁
    | n₁, .succ n₂ => .succ (add n₁ n₂)

  theorem addZero (n: Nat): add n .zero = n := rfl
  theorem addSucc (n₁ n₂: Nat): add n₁ n₂.succ = (add n₁ n₂).succ := rfl

  theorem zeroAdd: ∀ n: Nat, add .zero n = n
    | .zero => rfl
    | .succ n => congrArg Nat.succ (zeroAdd n)

  def mul: Nat → Nat → Nat
    | _, .zero => .zero
    | n₁, .succ n₂ => add (n₁.mul n₂) n₁

  theorem zeroAdd2: ∀ n: Nat, add .zero n = n
    | .zero => by simp [add]
    | .succ n => by simp [add, zeroAdd2]

  def add2 (n₁: Nat): Nat → Nat
    | .zero => n₁
    | .succ n₂ => (add2 n₁ n₂).succ

  def add3 (n₁ n₂: Nat): Nat :=
    match n₂ with
      | .zero => n₁
      | .succ n₂ => (add3 n₁ n₂).succ
end Hidden

def fib: Nat → Nat
  | 0 | 1 => 1
  | n + 2 => (fib (n + 1)) + fib n

example: fib 0 = 1 := rfl
example: fib 1 = 1 := rfl
example: fib (n + 2) = fib (n + 1) + fib n := rfl

example: fib 7 = 21 := rfl

def fibFast (n: Nat): Nat :=
  (loop n).2
  where
    loop: Nat → Nat × Nat
      | 0 => (0, 1)
      | n + 1 =>
        let p := loop n
        (p.2, p.1 + p.2)

def fibFastAlt (n: Nat): Nat :=
  let rec loop: Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2

section
  variable (C: Nat → Type u)

  #check (@Nat.below C: Nat → Type u)
  #reduce @Nat.below C (3: Nat)
  #check (@Nat.brecOn C: (n: Nat) → ((n: Nat) → @Nat.below C n → C n) → C n)
end

#reduce fib 50

def append: List α → List α → List α
  | [], l => l
  | hd::tl, l => hd :: append tl l

example: append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl

def listAdd [Add α]: List α → List α → List α
  | _, [] | [], _ => []
  | hd::tl, hd'::tl' => (hd + hd') :: listAdd tl tl'

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]

/-
## Local Recursive Declarations
-/

def replicate (n: Nat) (x: α): List α :=
  let rec loop: Nat → List α → List α
    | .zero, l => l
    | .succ n, l => loop n (x::l)
  loop n []

#check replicate
#check @replicate
#check replicate.loop
#check @replicate.loop

example (n: Nat) (x: α): (replicate n x).length = n :=
  let rec aux (n: Nat) (l: List α): (replicate.loop x n l).length = n + l.length :=
    match n with
      | .zero => by simp [replicate.loop]
      | .succ n => by simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  aux n []

def replicate2 (n: Nat) (x: α): List α :=
  loop n []
  where
    loop: Nat → List α → List α
      | .zero, l => l
      | .succ n, l => loop n (x::l)

example (n: Nat) (x: α): (replicate n x).length = n :=
  aux n []
  where
    aux (n: Nat) (l: List α): (replicate.loop x n l).length = n + l.length :=
      match n with
        | .zero => by simp [replicate.loop]
        | .succ n => by simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]

/-
## Well-Founded Recursion and Induction
-/

variable (ξ: Sort u)
variable (r: ξ → ξ → Prop)

#check Acc r
#check WellFounded r

theorem divLemma {x y: Nat}: 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨hylz, hylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le hylz hylex) hylz

def div.F (x: Nat) (f: (x₁: Nat) → x₁ < x → Nat → Nat) (y: Nat): Nat :=
  if h: 0 < y ∧ y ≤ x
  then f (x - y) (divLemma h) y + 1
  else Nat.zero

noncomputable def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2

def div2 (x y: Nat): Nat :=
  if h: 0 < y ∧ y ≤ x
  then
    have: x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div2 (x - y) y + 1
  else Nat.zero

example (x y: Nat): div2 x y = if 0 < y ∧ y ≤ x then div2 (x - y) y + 1 else 0 := by
  conv =>
    lhs
    unfold div2

example (x y: Nat) (h: 0 < y ∧ y ≤ x): div2 x y = div2 (x - y) y + 1 := by
  conv =>
    lhs
    unfold div2
  simp [h]

def Nat.toBin: Nat → List Nat
  | 0 => [0]
  | 1 => [1]
  | n + 2 =>
    have: (n + 2) / 2 < n + 2 := sorry
    Nat.toBin ((n + 2) / 2) ++ [n % 2]

#eval (1234567: Nat).toBin

def ack: Nat → Nat → Nat
  | 0, y => y + 1
  | x + 1, 0 => ack x 1
  | x + 1, y + 1 => ack x (ack (x + 1) y)
termination_by ack x y => (x, y)

def takeWhile {α: Type u} (p: α → Bool) (a: Array α): Array α :=
  go 0 #[]
  where
    go (i: Nat) (r: Array α): Array α :=
      if h: i < a.size
      then
        let elem := a.get ⟨i, h⟩
        if p elem
        then go (i + 1) (r.push elem)
        else r
      else r
termination_by go i r => a.size - i

def div3 (x y: Nat): Nat :=
  if h: 0 < y ∧ y ≤ x
  then div3 (x - y) y + 1
  else 0
decreasing_by apply divLemma; assumption

def ack2: Nat → Nat → Nat
  | 0, y => y + 1
  | x + 1, 0 => ack2 x 1
  | x + 1, y + 1 => ack2 x (ack2 (x + 1) y)
termination_by ack2 x y => (x, y)
decreasing_by
  simp_wf
  first | apply Prod.Lex.right; simp_arith
        | apply Prod.Lex.left; simp_arith

def unsound (x: Nat): False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
#print axioms unsound

/-
## Mutual Recursion
-/

mutual
  def even: Nat → Bool
    | 0 => true
    | n + 1 => odd n

  def odd: Nat → Bool
    | 0 => false
    | n + 1 => even n
end

example: even (n + 1) = odd n := by simp [even]
example: odd (n + 1) = even n := by simp [odd]

example (n: Nat): even n = not (odd n) := by
  induction n with
    | zero => rfl
    | succ _ _ => simp [even, odd, *]

mutual
  inductive Even: Nat → Prop where
    | zero: Even 0
    | succ: (n: Nat) → Odd n → Even (n + 1)
  inductive Odd: Nat → Prop where
    | succ: (n: Nat) → Even n → Odd (n + 1)
end

example: ¬(Odd 0) :=
  fun h => nomatch h

example: ∀ n: Nat, Odd (n + 1) → Even n
  | _, .succ _ h => h

example: ∀ n: Nat, Even (n + 1) → Odd n
  | _, .succ _ h => h

inductive Term where
  | const: String → Term
  | app: String → List Term → Term

mutual
  def Term.numConst: Term → Nat
    | .const _ => 1
    | .app _ ts => ts.numConst

  def List.numConst: List Term → Nat
    | [] => 0
    | hd :: tl => hd.numConst + tl.numConst
end

def sample := Term.app "f" [.app "g" [.const "x"], .const "y"]

#eval sample.numConst

mutual
  def Term.replaceConst (a b: String): Term → Term
    | .const c => if c = a then .const b else .const c
    | .app f args => .app f (args.replaceConst a b)

  def List.replaceConst (a b: String): List Term → List Term
    | [] => []
    | hd :: tl => hd.replaceConst a b :: tl.replaceConst a b
end

mutual
  theorem Term.numReplaceConst (a b: String) (t: Term): (t.replaceConst a b).numConst = t.numConst := by
    match t with
      | .const c => simp [Term.replaceConst]; split <;> simp [Term.numConst]
      | .app f args => simp [Term.replaceConst, Term.numConst, List.numReplaceConst a b args]

  theorem List.numReplaceConst (a b: String) (ts: List Term): (ts.replaceConst a b).numConst = ts.numConst := by
    match ts with
      | [] => simp [List.replaceConst, List.numConst]
      | hd :: tl => simp [List.replaceConst, List.numConst, Term.numReplaceConst a b hd, List.numReplaceConst a b tl]
end

/-
## Dependent Pattern Matching
-/

inductive Vector (α: Type u): Nat → Type u
  | nil: Vector α 0
  | cons: α → {n: Nat} → Vector α n → Vector α (n + 1)

#check @Vector.casesOn

def tail' (v: Vector α (n + 1)): Vector α n :=
  tailAux v rfl
  where
    tailAux {m: Nat} (v: Vector α m): m = n + 1 → Vector α n :=
      Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n)
        v
        (fun h: 0 = n + 1 => Nat.noConfusion h)
        (fun (_: α) (m: Nat) (as: Vector α m) =>
          fun (h: m + 1 = n + 1) =>
            Nat.noConfusion h (fun h₁: m = n => h₁ ▸ as))

namespace Hidden
  def head: {n: Nat} → Vector α (n + 1) → α
    | _, .cons hd _ => hd

  def tail: {n: Nat} → Vector α (n + 1) → Vector α n
    | _, .cons _ tl => tl

  example: ∀ {n: Nat} (v: Vector α (n + 1)), .cons (head v) (tail v) = v
    | _, .cons _ _ => rfl

  def map (f: α → β → γ): {n: Nat} → Vector α n → Vector β n → Vector γ n
    | 0, .nil, .nil => .nil
    | _ + 1, .cons hd tl, .cons hd' tl' => .cons (f hd hd') (map f tl tl')

  def zip: {n: Nat} → Vector α n → Vector β n → Vector (α × β) n
    | 0, .nil, .nil => .nil
    | _ + 1, .cons hd tl, .cons hd' tl' => .cons (hd, hd') (zip tl tl')

  #print map
  #print map.match_1
end Hidden

/-
## Inaccessible Patterns
-/

inductive ImageOf {α β: Type u} (f: α → β): β → Type u where
  | imf: (a: α) → ImageOf f (f a)

def ImageOf.inverseExplicit {f: α → β}: (b: β) → ImageOf f b → α
  | .(f a), imf a => a

def ImageOf.inverse {f: α → β}: (b: β) → ImageOf f b → α
  | _, imf a => a

def Vector.addExplicit [Add α]: {n: Nat} → Vector α n → Vector α n → Vector α n
  | 0, .nil, .nil => .nil
  | _ + 1, .cons hd tl, .cons hd' tl' => .cons (hd + hd') (addExplicit tl tl')

def Vector.addInaccessible [Add α]: {n: Nat} → Vector α n → Vector α n → Vector α n
  | .(_), .nil, .nil => .nil
  | .(_), .cons hd tl, .cons hd' tl' => .cons (hd + hd') (addInaccessible tl tl')

def Vector.add [Add α]: {n: Nat} → Vector α n → Vector α n → Vector α n
  | _, .nil, .nil => .nil
  | _, .cons hd tl, .cons hd' tl' => .cons (hd + hd') (add tl tl')

def Vector.addDiscriminantRefinement [Add α] {n: Nat}: Vector α n → Vector α n → Vector α n
  | .nil, .nil => .nil
  | .cons hd tl, .cons hd' tl' => .cons (hd + hd') (addDiscriminantRefinement tl tl')

def Vector.addAutoImplicitBounds [Add α]: Vector α n → Vector α n → Vector α n
  | .nil, .nil => .nil
  | .cons hd tl, .cons hd' tl' => .cons (hd + hd') (addAutoImplicitBounds tl tl')

def Vector.head: Vector α (n + 1) → α
  | .cons hd _ => hd

def Vector.tail: Vector α (n + 1) → Vector α n
  | .cons _ tl => tl

example: ∀ (v: Vector α (n + 1)), .cons v.head v.tail = v
  | .cons _ _ => rfl

def Vector.map (f: α → β → γ): Vector α n → Vector β n → Vector γ n
  | .nil, .nil => .nil
  | .cons hd tl, .cons hd' tl' => .cons (f hd hd') (tl.map f tl')

def Vector.zip: Vector α n → Vector β n → Vector (α × β) n
  | .nil, .nil => .nil
  | .cons hd tl, .cons hd' tl' => .cons (hd, hd') (tl.zip tl')

/-
## Match Expressions
-/

def isNotZero (m: Nat): Bool :=
  match m with
    | 0 => false
    | _ => true

def filter (p: α → Bool): List α → List α
  | [] => []
  | hd::tl =>
    match p hd with
      | true => hd :: filter p tl
      | _ => filter p tl

example: filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl

def foo5 (n: Nat) (b c: Bool) :=
  5 + match n - 5, b && c with
    | 0, true => 0
    | m + 1, true => m + 7
    | 0, false => 5
    | m + 1, false => m + 3

#eval foo5 7 true false

example: foo5 7 true false = 9 := rfl

def bar₁: Nat × Nat → Nat
  | (n₁, n₂) => n₁ + n₂

def bar₂ (p: Nat × Nat): Nat :=
  match p with
    | (n₁, n₂) => n₁ + n₂

def bar₃: Nat × Nat → Nat :=
  fun (n₁, n₂) => n₁ + n₂

def bar₄ (p: Nat × Nat): Nat :=
  let (n₁, n₂) := p
  n₁ + n₂

example (p: Nat × Nat): bar₁ p = bar₂ p := rfl
example (p: Nat × Nat): bar₁ p = bar₃ p := rfl
example (p: Nat × Nat): bar₁ p = bar₄ p := rfl
example (p: Nat × Nat): bar₂ p = bar₃ p := rfl
example (p: Nat × Nat): bar₂ p = bar₄ p := rfl
example (p: Nat × Nat): bar₃ p = bar₄ p := rfl

variable (p q: Nat → Prop)

example: (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨wx, hpx⟩, ⟨wy, hqy⟩ => ⟨wx, wy, hpx, hqy⟩

example (h₀: ∃ x, p x) (h₁: ∃ y, q y): ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
    | ⟨wx, hpx⟩, ⟨wy, hqy⟩ => ⟨wx, wy, hpx, hqy⟩

example: (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨wx, hpx⟩ ⟨wy, hqy⟩ => ⟨wx, wy, hpx, hqy⟩

example (h₀: ∃ x, p x) (h₁: ∃ y, q y): ∃ x y, p x ∧ q y :=
  let ⟨wx, hpx⟩ := h₀
  let ⟨wy, hqy⟩ := h₁
  ⟨wx, wy, hpx, hqy⟩

/-
## Local Recursive Declarations
-/

def replicate3 (n: Nat) (x: α): List α :=
  let rec loop: Nat → List α → List α
    | 0, l => l
    | n + 1, l => loop n (x::l)
  loop n []

#check @replicate3.loop

example (n: Nat) (x: α): (replicate3 n x).length = n := by
  let rec aux (n: Nat) (l: List α): (replicate3.loop x n l).length = n + l.length := by
    match n with
      | 0 => simp [replicate3.loop]
      | n + 1 => simp [replicate3.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []

def replicate4 (n: Nat) (x: α): List α :=
  loop n []
  where
    loop: Nat → List α → List α
      | 0, l => l
      | n + 1, l => loop n (x::l)

#check @replicate3.loop

example (n: Nat) (x: α): (replicate3 n x).length = n := by
  exact aux n []
  where
    aux (n: Nat) (l: List α): (replicate3.loop x n l).length = n + l.length := by
      match n with
        | 0 => simp [replicate3.loop]
        | n + 1 => simp [replicate3.loop, aux n, Nat.add_succ, Nat.succ_add]

/-
## Exercises
-/

section ExerciseOne
end ExerciseOne

section ExerciseTwo
end ExerciseTwo

section ExerciseThree
end ExerciseThree

section ExerciseFour
end ExerciseFour

section ExerciseFive
end ExerciseFive
