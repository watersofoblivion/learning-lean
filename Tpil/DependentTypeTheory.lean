/-
# Dependent Type Theory
-/

namespace DependentTypeTheory

/-
## Simple Type Theory
-/

def n₁: Nat := 1
def n₂: Nat := 0
def b₁: Bool := true
def b₂: Bool := false

#check n₁
#check n₂
#check n₂ + 0
#check n₁ + (n₂ + 0)
#check b₁
#check b₁ && b₂
#check b₁ || b₂
#check true

#eval 5 * 4
#eval n₁ + 2
#eval b₁ && b₂

#check Nat → Nat
#check Nat -> Nat

#check Nat × Nat
#check Prod Nat Nat

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat

#check Nat.succ
#check (0, 1)
#check Nat.add

#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#check (5, 9).1
#check (5, 9).2

#eval Nat.succ 2
#eval Nat.add 5 2
#eval (5, 9).1
#eval (5, 9).2

/-
## Types as Objects
-/

#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α: Type := Nat
def β: Type := Bool
def F: Type → Type := List
def G: Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G α
#check G α β
#check G α Nat

#check Prod α β
#check α × β

#check Prod Nat Nat
#check Nat × Nat

#check List α
#check List Nat

#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check Type 0

#check List
#check Prod

universe u
def F' (α: Type u): Type u := Prod α α
#check F

def F''.{v} (α: Type v): Type v := Prod α α
#check F''

/-
## Function Abstraction and Evaluation
-/

#check fun (x: Nat) => x + 5
#check λ (x: Nat) => x + 5
#check fun x: Nat => x + 5
#check λ x: Nat => x + 5

#eval (λ x: Nat => x + 5) 10

#check fun x: Nat => fun y: Bool => if not y then x + 1 else x + 2
#check fun (x: Nat) (y: Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

def f (n: Nat): String := toString n
def g (s: String): Bool := s.length > 0

#check fun x: Nat => x
#check fun _: Nat => true
#check fun x: Nat => (g ∘ f) x
#check fun x => (g ∘ f) x

#check fun (g: String → Bool) (f: Nat → String) (x: Nat) => (g ∘ f) x
#check fun (α β γ: Type) (g: β → γ) (f: α → β) (x: α) => (g ∘ f) x

#check (fun x: Nat => x) 1
#check (fun _: Nat => true) 1
#check (fun (α β γ: Type) (u: β → γ) (v: α → β) (x: α) => (u ∘ v) x) Nat String Bool g f 0

#eval (fun x: Nat => x) 1
#eval (fun _: Nat => true) 1

/-
## Definitions
-/

def _root_.Nat.double (n: Nat): Nat := n + n

#eval (3: Nat).double

def pi := 3.141592654

def add (n₁ n₂: Nat): Nat := n₁ + n₂

#eval add 2 3
#eval add ((3: Nat).double) (7 + 9)

def Nat.greater (n₁ n₂: Nat): Nat :=
  if n₁ > n₂ then n₁ else n₂

def twice (f: Nat → Nat) (n: Nat): Nat := (f ∘ f) n

#eval twice Nat.double 2

def compose (α β γ: Type) (g: β → γ) (f: α → β) (x: α): γ :=
  (g ∘ f) x

def Nat.square (n: Nat): Nat := n * n

#eval compose Nat Nat Nat Nat.double Nat.square 3

/-
## Local Definitions
-/

#check let y := 2 + 2; y * y
#eval let y := 2 + 2; y * y

def twiceDouble (x: Nat): Nat :=
  let y := x + x
  y * y

#eval twiceDouble 2

#check let y := 2 + 2; let z := y + y; z * z * z
#eval let y := 2 + 2; let z := y + y; z * z

def foo :=
  let a := Nat
  fun x: a => x + 2

/-
# Variables and Sections
-/

section Variables
  variable (α β γ: Type)
  variable (g: β → α) (f: α → β) (h: α → α)
  variable (x: α)

  def Variables.compose := (g ∘ f) x
  def Variables.doTwice := (h ∘ h) x
  def Variables.doThrice := (h ∘ h ∘ h) x

  #print Variables.compose
  #print Variables.doTwice
  #print Variables.doTwice
end Variables

/-
# Namespaces
-/

namespace Foo
  def a: Nat := 5
  def f (x: Nat): Nat := x + 7

  def fa: Nat := f a
  def ffa: Nat := (f ∘ f) a

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check ffa

#check List.nil
#check List.cons
#check List.map

open List

#check nil
#check cons
#check map

namespace Foo
  namespace Bar
    def ffa: Nat := (f ∘ f) a

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa

/-
## What Makes Dependent Type Theory Dependent?
-/

def cons (α: Type) (x: α) (l: List α): List α :=
  List.cons x l

#check cons Nat
#check cons Bool
#check cons

#check @List.cons
#check @List.nil
#check @List.length
#check @List.append

universe s t

def fDep (α: Type s) (β: α → Type t) (a: α) (b: β a): (a: α) × β a :=
  ⟨a, b⟩

def gDep (α: Type s) (β: α → Type t) (a: α) (b: β a): Σ a: α, β a :=
  Sigma.mk a b

def h₁ (n: Nat): Nat :=
  (fDep Type id Nat n).2

#eval h₁ 5

def h₂ (n: Nat): Nat :=
  (gDep Type id Nat n).2

#eval h₂ 5

/-
## Implicit Arguments
-/

#check id
#check id 1
#check id "hello"
#check @id

universe q

section
  variable {α: Type q}
  variable (x: α)

  def ident := x
end

#check ident
#check ident 4
#check ident "hello"

#check List.nil
#check id

#check (List.nil: List Nat)
#check (id: Nat → Nat)

#check 2
#check (2: Nat)
#check (2: Int)

#check @id
#check @id Nat
#check @id Bool

#check @id Nat 1
#check @id Bool true

end DependentTypeTheory
