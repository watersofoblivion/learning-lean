/-
# Tactics
-/

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro hp
  exact ⟨hq, hp⟩

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  · apply And.intro
    · exact hq
    · exact hp

/-
## Basic Tactics
-/

example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    apply Or.elim h.right
    · intro hq
      apply Or.inl
      apply And.intro
      · exact h.left
      · exact hq
    · intro hr
      apply Or.inr
      apply And.intro
      · exact h.left
      · exact hr
  · intro h
    apply Or.elim h
    · intro hpq
      apply And.intro
      · exact hpq.left
      · apply Or.inl
        exact hpq.right
    · intro hpr
      apply And.intro
      · exact hpr.left
      · apply Or.inr
        exact hpr.right

example (α: Type): α → α := by
  intro a
  exact a

example (α: Type): ∀ x: α, x = x := by
  intro x
  exact Eq.refl x

example: ∀ a b c: Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

example (α: Type) (p q: α → Prop): (∃ x: α, p x ∧ q x) → ∃ x: α, q x ∧ p x := by
  intro ⟨w, ⟨hpx, hqx⟩⟩
  exact ⟨w, ⟨hqx, hpx⟩⟩

example (α: Type) (p q: α → Prop): (∃ x: α, p x ∨ q x) → ∃ x: α, q x ∨ p x := by
  intro
    | ⟨w, .inl hpx⟩ => exact ⟨w, .inr hpx⟩
    | ⟨w, .inr hqx⟩ => exact ⟨w, .inl hqx⟩

example (w x y z: Nat) (h₁: x = y) (h₂: y = z) (h₃: z = w): x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption

example (w x y z: Nat) (h₁: x = y) (h₂: y = z) (h₃: z = w): x = w := by
  apply Eq.trans
  · assumption
  · apply Eq.trans
    · assumption
    · assumption

example: ∀ a b c: Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  · apply Eq.symm
    · assumption
  · assumption

example: ∀ a b c: Nat, a = b → a = c → c = b := by
  unhygienic
  intros
  apply Eq.trans
  · apply Eq.symm
    · exact a_2
  · exact a_1

example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  · apply Eq.symm
    · exact h2
  · exact h1

example (x: Nat): x = x := by
  rfl

example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

example (x: Nat): x = x := by
  revert x
  intro y
  rfl

example (x y: Nat) (h: x = y): y = x := by
  revert h
  intro h₁
  apply Eq.symm
  exact h₁

example (x y: Nat) (h: x = y): y = x := by
  revert x y
  intros
  apply Eq.symm
  assumption

example: 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

example: 2 + 3 = 5 := by
  generalize h: 3 = x
  rw [← h]

/-
## More Tactics
-/

example (p q: Prop): p ∨ q → q ∨ p := by
  intro h
  cases h with
    | inl hp => apply Or.inr; exact hp
    | inr hq => apply Or.inl; exact hq

example (p q: Prop): p ∨ q → q ∨ p := by
  intro h
  cases h
  · apply Or.inr
    assumption
  · apply Or.inl
    assumption

example (p q: Prop): p ∨ q → q ∨ p := by
  intro h
  cases h
  case inl =>
    apply Or.inr
    assumption
  case inr =>
    apply Or.inl
    assumption

example (p: Prop): p ∨ p → p := by
  intro h
  cases h
  repeat assumption

example (p: Prop): p ∨ p → p := by
  intro h
  cases h <;> assumption

example (p q: Prop): p ∧ q → q ∧ p := by
  intro h
  cases h with
    | intro hp hq =>
      constructor
      exact hq
      exact hp

example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h with
      | intro hp hqr =>
        cases hqr
        · apply Or.inl; constructor <;> assumption
        · apply Or.inr; constructor <;> assumption
  · intro h
    cases h with
      | inl hpq =>
        cases hpq with
          | intro hp hq =>
            constructor
            · exact hp
            · apply Or.inl; exact hq
      | inr hpr =>
        cases hpr with
          | intro hp hr =>
            constructor
            · exact hp
            · apply Or.inr; exact hr

example (p q: Nat → Prop): (∃ x: Nat, p x) → ∃ x: Nat, p x ∨ q x := by
  intro h
  cases h with
    | intro x hpx =>
      constructor
      apply Or.inl
      exact hpx

example (p q: Nat → Prop): (∃ x: Nat, p x) → ∃ x: Nat, p x ∨ q x := by
  intro h
  cases h with
    | intro x hpx =>
      exists x
      apply Or.inl
      exact hpx

example (p q: Nat → Prop): (∃ x: Nat, p x ∧ q x) → ∃ x: Nat, q x ∧ p x := by
  intro h
  cases h with
    | intro w hpq =>
      cases hpq with
        | intro hpw pqw =>
          exists w

def swapPair: α × β → β × α := by
  intro h
  cases h
  constructor <;> assumption

def swapSum: Sum α β → Sum β α := by
  intro h
  cases h with
    | inl a =>
      apply Sum.inr
      assumption
    | inr b =>
      apply Sum.inl
      assumption

example (P: Nat → Prop) (h₀: P 0) (h₁: ∀ n: Nat, P n.succ) (m: Nat): P m := by
  cases m with
    | zero => exact h₀
    | succ n => exact h₁ n

example (p q: Prop): p ∧ ¬p → q := by
  intro h
  cases h with
    | intro hp hnp => contradiction

example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    match h with
      | ⟨_, .inl _⟩ =>
        apply Or.inl
        constructor <;> assumption
      | ⟨_, .inr _⟩ =>
        apply Or.inr
        constructor <;> assumption
  · intro h
    match h with
      | .inl ⟨hp, hq⟩ =>
        constructor
        exact hp
        apply Or.inl
        exact hq
      | .inr ⟨hp, hr⟩ =>
        constructor
        exact hp
        apply Or.inr
        exact hr

example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro
    | ⟨hp, .inl hq⟩ =>
      apply Or.inl
      constructor <;> assumption
    | ⟨hp, .inr hr⟩ =>
      apply Or.inr
      constructor <;> assumption
  . intro
    | .inl ⟨hp, hq⟩ =>
      constructor
      · assumption
      · apply Or.inl
        assumption
    | .inr ⟨hp, hr⟩ =>
      constructor
      · assumption
      · apply Or.inr
        assumption

/-
## Structuring Tactic Proofs
-/

example (p q r: Prop): p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp: p := h.left
    have hqr: q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
        | inl hq => exact .inl ⟨hp, hq⟩
        | inr hr => exact .inr ⟨hp, hr⟩

example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h.right with
      | inl hq => exact (.inl ⟨h.left, hq⟩)
      | inr hr => exact (.inr ⟨h.left, hr⟩)
  · intro h
    cases h with
      | inl hpq => exact ⟨hpq.left, .inl hpq.right⟩
      | inr hpr => exact ⟨hpr.left, .inr hpr.right⟩

example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h
    cases h.right with
      | inl hq =>
        show (p ∧ q) ∨ (p ∧ r)
        exact Or.inl ⟨h.left, hq⟩
      | inr hr =>
        show (p ∧ q) ∨ (p ∧ r)
        exact Or.inr ⟨h.left, hr⟩
  · intro h
    cases h with
      | inl hpq =>
        show p ∧ (q ∨ r)
        exact ⟨hpq.left, Or.inl hpq.right⟩
      | inr hpr =>
        show p ∧ (q ∨ r)
        exact ⟨hpr.left, Or.inr hpr.right⟩

example (n: Nat): n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

example (p q r: Prop): p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
    | inl hq =>
      have hpq: p ∧ q := ⟨hp, hq⟩
      apply Or.inl
      exact hpq
    | inr hr =>
      have hpr: p ∧ r := ⟨hp, hr⟩
      apply Or.inr
      exact hpr

example (p q r: Prop): p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
    | inl hq =>
      have: p ∧ q := ⟨hp, hq⟩
      apply Or.inl
      exact this
    | inr hr =>
      have: p ∧ r := ⟨hp, hr⟩
      apply Or.inr
      exact this

 example (p q r: Prop): p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
    | inl hq =>
      have := And.intro hp hq
      apply Or.inl
      exact this
    | inr hr =>
      have := And.intro hp hr
      apply Or.inr
      exact this

example: ∃ x, x + 2 = 8 := by
  let a: Nat := 2 * 3
  exists a

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ }}
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ }}

/-
## Tactic Combinators
-/

example (p q: Prop) (hp: p): p ∨ q := by
  apply Or.inl; assumption

example (p q: Prop) (hp: p) (hq: q): p ∧ q := by
  constructor <;> assumption

example (p q: Prop) (hp: p): p ∨ q := by
  first | apply Or.inl; assumption
        | apply Or.inr; assumption

example (p q: Prop) (hq: q): p ∨ q := by
  first | apply Or.inl; assumption
        | apply Or.inr; assumption

example (p q r: Prop) (hp: p): p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption
                | apply Or.inr
                | assumption)

example (p q r: Prop) (hq: q): p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption
                | apply Or.inr
                | assumption)

example (p q r: Prop) (hr: r): p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption
                | apply Or.inr
                | assumption)

example (p q r: Prop) (hp: p) (hq: q) (hr: r): p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

example (p q r: Prop) (hp: p) (hq: q) (hr: r): p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

example (p q r: Prop) (hp: p) (hq: q) (hr: r): p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

example (p q r: Prop) (hp: p) (hq: q) (hr: r): p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor
                           | assumption))

/-
## Rewriting
-/

example (f: Nat → Nat) (k: Nat) (h₁: f 0 = 0) (h₂: k = 0): f k = 0 := by
  rw [h₂]
  rw [h₁]

example (x y: Nat) (p: Nat → Prop) (q: Prop) (h₁: q → x = y) (h₂: p y) (hq: q): p x := by
  rw [h₁ hq]
  exact h₂

example (f: Nat → Nat) (k: Nat) (h₁: f 0 = 0) (h₂: k = 0): f k = 0 := by
  rw [h₂, h₁]

example (f: Nat → Nat) (k: Nat) (h₁: f 0 = 0) (h₂: k = 0): f k = 0 := by
  rw [← h₁, h₂]

example (a b c: Nat): a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c: Nat): a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c: Nat): a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

example (f: Nat → Nat) (a: Nat) (h: a + 0 = 0): f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

def Tuple (α: Type) (n: Nat) :=
  { as: List α // as.length = n }

example (n: Nat) (h: n = 0) (t: Tuple α n): Tuple α 0 := by
  rw [h] at t
  exact t

/-
## Using the Simplifier
-/

example (x y z: Nat): (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp
example (x y z: Nat) (p: Nat → Prop) (h: p (x * y)): p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp
  assumption

example (xs: List Nat): List.reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ List.reverse xs := by
  simp
example (xs ys: List α): List.length (List.reverse (xs ++ ys)) = xs.length + ys.length := by
  simp [Nat.add_comm]

example (x y z: Nat) (p: Nat → Prop) (h: p ((x + 0) * (0 + y * 1 + z * 0))): p (x * y) := by
  simp at h
  assumption

attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z: Nat) (p: Nat → Prop) (h: p (x * y + z * w * x)): p (x * w * z + y * x) := by
  simp at *
  assumption
example (x y z: Nat) (p: Nat → Prop) (h₁: p (1 * x + y)) (h₂: p (x * z * 1)): p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption

example (w x y z: Nat): x * y + z * w * x = x * w * z + y * x := by
  simp
example (w x y z: Nat) (p: Nat → Prop) (h: p (x * y + z * w * x)): p (x * w * z + y * x) := by
  simp
  simp at h
  assumption

def f (m n: Nat): Nat := m + n + m

example {m n: Nat} (h₁: n = 1) (h₂: 0 = m): (f m n) = n := by
  simp [h₁, ←h₂, f]

example (f: Nat → Nat) (k: Nat) (h₁: f 0 = 0) (h₂: k = 0): f k = 0 := by
  simp [h₁, h₂]
example (f: Nat → Nat) (k: Nat) (h₁: f 0 = 0) (h₂: k = 0): f k = 0 := by
  simp [*]

example (u w x y z: Nat) (h₁: x = y + z) (h₂: w = u + x): w = z + y + u := by
  simp [*]

example (p q: Prop) (hp: p): p ∧ q ↔ q := by
  simp [*]
example (p q: Prop) (hp: p): p ∨ q := by
  simp [*]
example (p q r: Prop) (hp: p) (hq: q): p ∧ (q ∨ r) := by
  simp [*]

example (x₁ x₂ y₁ y₂: Nat) (h₁: x₁ + 0 = x₂) (h₂: y₁ + 0 = y₂): x₁ + y₁ + 0 = x₂ + y₂ := by
  simp at *
  simp [*]

def List.mkSymm (xs: List α) := xs ++ xs.reverse

theorem reverseMkSymm (l: List α): l.mkSymm.reverse = l.mkSymm := by
  simp [List.mkSymm]

example (l₁ l₂: List α): (l₁ ++ l₂.mkSymm).reverse = l₂.mkSymm ++ l₁.reverse := by
  simp [reverseMkSymm]
example (l₁ l₂: List α) (p: List α → Prop) (h: p (l₁ ++ l₂.mkSymm).reverse): p (l₂.mkSymm ++ l₁.reverse) := by
  simp [reverseMkSymm] at h
  assumption

section
  attribute [local simp] reverseMkSymm

  example (l₁ l₂: List α): (l₁ ++ l₂.mkSymm).reverse = l₂.mkSymm ++ l₁.reverse := by
    simp
  example (l₁ l₂: List α) (p: List α → Prop) (h: p (l₁ ++ l₂.mkSymm).reverse): p (l₂.mkSymm ++ l₁.reverse) := by
    simp at h
    assumption
end

example: 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp_arith

/-
## Split Tactic
-/

def testFun (x y z: Nat): Nat :=
  match x, y, z with
    | 5, _, _ => y
    | _, 5, _ => y
    | _, _, 5 => y
    | _, _, _ => 1

example (x y z: Nat): x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → testFun x y w = 1 := by
  intros
  simp [testFun]
  split
  · contradiction
  · contradiction
  · contradiction
  . rfl

example (x y z: Nat): x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → testFun x y w = 1 := by
  intros; simp [testFun]; split <;>
    first | contradiction
          | rfl

def g: List Nat → List Nat → Nat
  | [a, b], _ => a + b + 1
  | _, [b, _] => b + 1
  | _, _      => 1

example (l₁ l₂: List Nat) (h: g l₁ l₂ = 0): False := by
  simp [g] at h
  split at h <;> simp_arith at *

/-
## Extensible Tactics
-/

syntax "triv": tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h: p): p := by
  triv

macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x: α): x = x := by
  triv

example (x: α) (h: p): x = x ∧ p := by
  apply And.intro <;> triv
example (x: α) (h: p): x = x ∧ p :=
  ⟨Eq.refl x, h⟩

macro_rules
  | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x: α) (h: p): x = x ∧ p := by
  triv

/-
## Exercises
-/

section ExerciseOne
end ExerciseOne

section ExerciseTwo
  example (p q r: Prop) (hp: p): (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
    simp [hp]

  example (p q r: Prop) (hp: p): (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
    ⟨.inl hp, .inr (.inl hp), .inr (.inr hp)⟩
end ExerciseTwo
