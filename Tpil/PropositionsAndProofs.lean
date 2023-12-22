/-
# Propositions and Proofs
-/

namespace PropositionsAndProofs

/-
## Propositions as Types
-/

#check And
#check Or
#check Not
-- #check Implies

variable (p q r s: Prop)
#check And p q
#check Or (And p q) r
#check (And p q) → (And q p)

/-
## Working with Propositions as Types
-/

theorem t₁ {p q: Prop} (h₁: p) (_: q): p :=
  show p from h₁

#print t₁

theorem t₂ {p q: Prop} (h₁: p): q → p :=
  t₁ h₁

#check @t₁ p q
#check @t₁ r s
#check @t₁ (r → s) (s → r)

section
  variable (h: r → s)
  #check @t₁ (r → s) (s → r) h
section

theorem t₃ {p q r: Prop} (h₁: q → r) (h₂: p → q) (h₃: p): r :=
  show r from (h₁ ∘ h₂) h₃

/-
## Propositional Logic
-/

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

/-
### Conjunction
-/

example (hp: p) (hq: q): p ∧ q := ⟨hp, hq⟩

#check fun (hp: p) (hq: q) => And.intro hp hq

example (h: p ∧ q): p := h.left
example (h: p ∧ q): q := h.right
example: p ∧ q → q ∧ p
  | ⟨hp, hq⟩ => ⟨hq, hp⟩

example: p ∧ q → q ∧ p ∧ q
  | ⟨hp, hq⟩ => ⟨hq, hp, hq⟩

/-
### Disjunction
-/

example (hp: p): p ∨ q := Or.intro_left q hp
example (hq: q): p ∨ q := Or.intro_right p hq
example: p ∨ q → q ∨ p
  | .inl hp => .inr hp
  | .inr hq => .inl hq

/-
### Negation and Falsity
-/

example (hpq: p → q) (hnq: ¬q): ¬p :=
  fun hp: p =>
    show False from hnq (hpq hp)

example (hp: p) (hnp: ¬p): q := False.elim (hnp hp)
example (hp: p) (hnp: ¬p): q := absurd hp hnp

example (hnp: ¬p) (hq: q) (hqp: q → p): r :=
  absurd (hqp hq) hnp

/-
### Logical Equivalence
-/

theorem And.swap: p ∧ q ↔ q ∧ p :=
  have mp (h: p ∧ q): q ∧ p := ⟨h.right, h.left⟩
  have mpr (h: q ∧ p): p ∧ q := ⟨h.right, h.left⟩
  ⟨mp, mpr⟩

example: p ∧ q ↔ q ∧ p :=
  have mp: p ∧ q → q ∧ p
      | .intro hp hq => ⟨hq, hp⟩
  have mpr: q ∧ p → p ∧ q
      | .intro hq hp => ⟨hp, hq⟩
  ⟨mp, mpr⟩

example: p ∧ q ↔ q ∧ p :=
  have mp: p ∧ q → q ∧ p
    | ⟨hp, hq⟩ => ⟨hq, hp⟩
  have mpr: q ∧ p → p ∧ q
    | ⟨hq, hp⟩ => ⟨hp, hq⟩
  ⟨mp, mpr⟩

#check And.swap p q

section
  variable (h: p ∧ q)
  example: q ∧ p :=
    (And.swap p q).mp h
section

/-
## Introducing Auxiliary Subgoals
-/

example (h: p ∧ q): q ∧ p :=
  have hp: p := h.left
  have hq: q := h.right
  show q ∧ p from ⟨hq, hp⟩

example (h: p ∧ q): q ∧ p :=
  have hp: p := h.left
  suffices hq: q from ⟨hq, hp⟩
  show q from h.right

/-
## Classical Logic
-/

section
  open Classical

  #check em p

  theorem doubleNeg {p: Prop} (h: ¬¬p): p :=
    match em p with
      | .inl hp => hp
      | .inr hnp => absurd hnp h

  -- example (h: ¬¬p): p :=
  --   have p (hp: p) := hp
  --   have notP (hnp: ¬p) := absurd hnp h
  --   byCases p notP

  example {p: Prop} (h: ¬¬p): p :=
    have proof (hnp: ¬p) := h hnp
    byContradiction proof

  example (h: ¬(p ∧ q)): ¬p ∨ ¬q :=
    match (em p) with
      | .inl hp =>
        have hnq: ¬q := fun hq: q => h ⟨hp, hq⟩
        .inr hnq
      | .inr hnp => .inl hnp
end

/-
## Examples of Propositional Validities
-/

example: p ∧ q ↔ q ∧ p :=
  have mp: p ∧ q → q ∧ p
    | ⟨hp, hq⟩ => ⟨hq, hp⟩
  have mpr: q ∧ p → p ∧ q
    | ⟨hq, hp⟩ => ⟨hp, hq⟩
  ⟨mp, mpr⟩

example: p ∨ q ↔ q ∨ p :=
  have mp: p ∨ q → q ∨ p
    | .inl hp => .inr hp
    | .inr hq => .inl hq
  have mpr: q ∨ p → p ∨ q
    | .inl hq => .inr hq
    | .inr hp => .inl hp
  ⟨mp, mpr⟩

example: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have mp: (p ∧ q) ∧ r → p ∧ (q ∧ r)
    | ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, ⟨hq, hr⟩⟩
  have mpr: p ∧ (q ∧ r) → (p ∧ q) ∧ r
    | ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩
  ⟨mp, mpr⟩

example: (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  have mp: (p ∨ q) ∨ r → p ∨ (q ∨ r)
    | .inl (.inl hp) => .inl hp
    | .inl (.inr hq) => .inr (.inl hq)
    | .inr hr => .inr (.inr hr)
  have mpr: p ∨ (q ∨ r) → (p ∨ q) ∨ r
    | .inl hp => .inl (.inl hp)
    | .inr (.inl hq) => .inl (.inr hq)
    | .inr (.inr hr) => .inr hr
  ⟨mp, mpr⟩

example: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have mp: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r)
    | ⟨hp, (.inl hq)⟩ => .inl ⟨hp, hq⟩
    | ⟨hp, (.inr hr)⟩ => .inr ⟨hp, hr⟩
  have mpr: (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r)
    | .inl ⟨hp, hq⟩ => ⟨hp, .inl hq⟩
    | .inr ⟨hp, hr⟩ => ⟨hp, .inr hr⟩
  ⟨mp, mpr⟩

example: p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  have mp: p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
    | .inl hp => ⟨.inl hp, .inl hp⟩
    | .inr ⟨hq, hr⟩ => ⟨.inr hq, .inr hr⟩
  have mpr: (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
    | ⟨.inl hp, _⟩ | ⟨_, .inl hp⟩ => .inl hp
    | ⟨.inr hq, .inr hr⟩ => .inr ⟨hq, hr⟩
  ⟨mp, mpr⟩

example: p → q → r ↔ (p ∧ q) → r :=
  have mp (h: p → q → r) :=
    fun ⟨hp, hq⟩ => h hp hq
  have mpr (h: (p ∧ q) → r) :=
    fun hp hq => h ⟨hp, hq⟩
  ⟨mp, mpr⟩

example: (p ∨ q) → r ↔ (p → r) ∧ (q → r) :=
  have mp (h: (p ∨ q) → r) :=
    have left (hp: p): r := h (.inl hp)
    have right (hq: q): r := h (.inr hq)
    ⟨left, right⟩
  have mpr: (p → r) ∧ (q → r) → (p ∨ q) → r
    | ⟨pr, qr⟩ =>
      have: p ∨ q → r
        | .inl hp => pr hp
        | .inr hq => qr hq
      this
  ⟨mp, mpr⟩

example: ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have mp (h: ¬(p ∨ q)) :=
    have left (hp: p) := h (.inl hp)
    have right (hq: q) := h (.inr hq)
    ⟨left, right⟩
  have mpr (h: ¬p ∧ ¬q) :=
    fun
      | .inl hp => h.left hp
      | .inr hq => h.right hq
  ⟨mp, mpr⟩

example: ¬p ∨ ¬q ↔ ¬(p ∧ q) :=
  have mp: ¬p ∨ ¬q → ¬(p ∧ q)
    | .inl hnp => fun (hpq: p ∧ q) => False.elim (hnp hpq.left)
    | .inr hnq => fun (hpq: p ∧ q) => False.elim (hnq hpq.right)
  have mpr (hnpq: ¬(p ∧ q)) := sorry
  ⟨mp, mpr⟩

example: ¬(p ∧ ¬p) :=
  fun ⟨hp, hnp⟩ => absurd hp hnp

example: p ∧ ¬q → ¬(p → q)
  | ⟨hp, hnq⟩ =>
    fun (hpq: p → q) => absurd (hpq hp) hnq

example (hnp: ¬p) (hp: p): q := absurd hp hnp

example: ¬p ∨ q → p → q
  | .inl hnp, hp => absurd hp hnp
  | .inr hq, _ => hq

example: p ∨ False ↔ p :=
  have mp: p ∨ False → p
    | .inl hp => hp
    | .inr hf => False.elim hf
  have mpr (hp: p) := .inl hp
  ⟨mp, mpr⟩

example: p ∧ False ↔ False :=
  have mp: p ∧ False → False
    | ⟨_, hf⟩ => False.elim hf
  have mpr (hf: False) := False.elim hf
  ⟨mp, mpr⟩

example: ¬(p ↔ ¬p) :=
  fun pnp: (p ↔ ¬p) =>
    have mp: p → ¬p := sorry
    have mpr: ¬p → p := sorry
    show False from sorry

example (hpq: p → q) (hnq: ¬q): ¬p :=
  fun (hp: p) => absurd (hpq hp) hnq

section
  open Classical

  example (hprs: p → r ∨ s): ((p → r) ∨ (p → s)) := sorry

/-
  example: ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example: ¬(p → q) → p ∧ ¬q := sorry
  example: (p → q) → (¬p ∨ q) := sorry
  example: (¬q → ¬p) → (p → q) := sorry
-/
  example: p ∨ ¬p := em p
/-
  example: (((p → q) → p) → p) := sorry
-/
end

end
