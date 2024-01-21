/-
# Proof Objects
-/

import «SoftwareFoundations».«LogicalFoundations».«IndProp»

#check Even.succSucc

example: Even 4 := by
  apply Even.succSucc
  · apply Even.succSucc
    · apply Even.zero

example: Even 4 :=
  Even.zero
    |> Even.succSucc 0
    |> Even.succSucc 2

example: Even 4 := by
  apply Even.succSucc 2 (Even.succSucc 0 Even.zero)

/-
## Proof Scripts
-/

def even4: Even 4 :=
  Even.zero
    |> Even.succSucc 0
    |> Even.succSucc 2

#print even4
#print even4.proof_1


example: Even 8 := by
  apply Even.succSucc
  · apply Even.succSucc
    · apply Even.succSucc
      · apply Even.succSucc
        · apply Even.zero

example: Even 8 :=
  Even.zero
    |> Even.succSucc 0
    |> Even.succSucc 2
    |> Even.succSucc 4
    |> Even.succSucc 6

/-
## Quantifiers, Implications, and Functions
-/

example {n: Nat} (h: Even n): Even (n + 4) := by
  apply Even.succSucc
  · apply Even.succSucc
    . exact h

example {n: Nat} (h: Even n): Even (n + 4) :=
  h
    |> Even.succSucc n
    |> Even.succSucc (n + 2)

/-
## Programming with Tactics
-/

def add1: Nat → Nat := by
  intro n
  apply Nat.succ
  exact n

#print add1

example: add1 41 = 42 := rfl

/-
## Logical Connectives as Inductive Types
-/

namespace Props
  /-
  ### Conjunction
  -/
  namespace And
    inductive And (P Q: Prop): Prop where
      | intro: P → Q → And P Q

    example {P Q: Prop} (h: And P Q): P := by
      cases h with
        | intro hp _ => exact hp

    example {P Q: Prop}: And P Q → P
      | .intro hp _ => hp

    example {P Q: Prop}: And P Q ↔ And Q P := by
      apply Iff.intro
      · intro h
        cases h with
          | intro hp hq =>
            apply And.intro
            · exact hq
            · exact hp
      · intro h
        cases h with
          | intro hq hp =>
            apply And.intro
            · exact hp
            · exact hq

    example {P Q: Prop}: And P Q ↔ And Q P :=
      have mp: And P Q → And Q P
        | ⟨hp, hq⟩ => ⟨hq, hp⟩
      have mpr: And Q P → And P Q
        | ⟨hq, hp⟩ => ⟨hp, hq⟩
      ⟨mp, mpr⟩

    example {P Q R: Prop} (h₁: And P Q) (h₂: And Q R): And P R := by
      apply And.intro
      · cases h₁ with
          | intro hp _ => exact hp
      · cases h₂ with
          | intro _ hr => exact hr

    example {P Q R: Prop}: And P Q → And Q R → And P R
      | ⟨hp, _⟩, ⟨_, hr⟩ => ⟨hp, hr⟩
  end And

  /-
  ### Disjunction
  -/
  namespace Or
    inductive Or (P Q: Prop): Prop where
      | inl: P → Or P Q
      | inr: Q → Or P Q

    example {P Q: Prop} (h: P): Or P Q := by
      exact .inl h

    example {P Q: Prop}: P → Or P Q
      | h => .inl h

    example {P Q R: Prop} (h₁: Or P Q) (h₂: P → R) (h₃: Q → R): R := by
      cases h₁ with
        | inl hp => exact h₂ hp
        | inr hq => exact h₃ hq

    example {P Q R: Prop}: Or P Q → (P → R) → (Q → R) → R
      | .inl hp, hpr, _ => hpr hp
      | .inr hq, _, hqr => hqr hq

    example {P Q: Prop} (h: Or P Q): Or Q P := by
      cases h with
        | inl hp => exact .inr hp
        | inr hq => exact .inl hq

    example {P Q: Prop}: Or P Q → Or Q P
      | .inl hp => .inr hp
      | .inr hq => .inl hq
  end Or

  /-
  ## Existential Quantification
  -/
  namespace Ex
    inductive Exists (P: α → Prop): Prop where
      | intro (x: α) (h: P x): Exists P

    #check Exists (fun n => Even n)

    example: ∃ n: Nat, Even n := ⟨0, Even.zero⟩
    example: ∃ n: Nat, Even n := ⟨2, Even.succSucc 0 Even.zero⟩
    example: ∃ n: Nat, Even n := ⟨4, Even.succSucc 2 (Even.succSucc 0 Even.zero)⟩

    example: Exists (fun n: Nat => Even n.succ) :=
      Exists.intro 1 (Even.succSucc 0 Even.zero)
  end Ex

  /-
  ## True and False
  -/
  namespace TrueFalse
    inductive True: Prop where
      | tt: True

    example {P: Prop} (_: P): True := by
      exact True.tt

    example {P: Prop}: P → True
      | _ => True.tt

    inductive False: Prop

    #check_failure (1 = 0: False)

    example (h: False): 1 = 0 := by
      cases h

    example {P: Prop} (h: False): P := by
      cases h
  end TrueFalse
end Props

/-
## Equality
-/

namespace Ekwal
  inductive Eq: α → α → Prop where
    | refl (x: α): Eq x x

  example: Eq (2 + 2) (1 + 3) := Eq.refl 4

  example: Eq (2 + 2) (1 + 3) := by
    apply Eq.refl

  example {x: α}: Eq ([] ++ [x]) ([x] ++ []) := Eq.refl [x]

  example {x: α}: Eq ([] ++ [x]) ([x] ++ []) := by
    apply Eq.refl

  example {n₁ n₂: Nat}: Eq n₁ n₂ → Eq n₁.succ n₂.succ
    | .refl _ => .refl _

  example {n₁ n₂: Nat} (h: Eq n₁ n₂): Eq n₁.succ n₂.succ := by
    cases h with
      | refl => apply Eq.refl

  example {hd₁ hd₂: α} {tl₁ tl₂: List α} (h₁: Eq hd₁ hd₂) (h₂: Eq tl₁ tl₂): Eq (hd₁ :: tl₁) (hd₂ :: tl₂) := by
    cases h₁ with
      | refl =>
        cases h₂ with
          | refl => apply Eq.refl

  example {hd₁ hd₂: α} {tl₁ tl₂: List α}: Eq hd₁ hd₂ → Eq tl₁ tl₂ → Eq (hd₁ :: tl₁) (hd₂ :: tl₂)
    | .refl _, .refl _ => .refl _

  example {x y: α} (h₁: Eq x y): ∀ P: α → Prop, P x → P y := by
    intro P
    intro h₂
    sorry

  -- example {x y: α}: Eq x y → ∀ P: α → Prop, P x → P y
  --   | .refl _, fp, hpx => P

  example {x y: α} (h₁: ∀ P: α → Prop, P x → P y): Eq x y := by
    sorry

  example {x y: α}: ∀ P: α → Prop, P x → P y → Eq x y :=
    sorry
end Ekwal

/-
### Inversion, Again
-/

/-
## Coq's (Lean's) Trusted Computing Base
-/

/-
## More Exercies
-/

example {P Q R: Prop}: P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
  | ⟨hp, ⟨hq, hr⟩⟩ => ⟨⟨hp, hq⟩, hr⟩

example {P Q R: Prop}: P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  have mp: P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
    | .inl hp => ⟨.inl hp, .inl hp⟩
    | .inr ⟨hq, hr⟩ => ⟨.inr hq, .inr hr⟩
  have mpr: (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)
    | ⟨.inl hp, _⟩ => .inl hp
    | ⟨_, .inl hp⟩ => .inl hp
    | ⟨.inr hq, .inr hr⟩ => .inr ⟨hq, hr⟩
  ⟨mp, mpr⟩

example {P: Prop}: P → ¬¬P
  | h => sorry

example {P Q: Prop}: (P ∧ ¬P) → Q
  | ⟨hp, hnp⟩ => absurd hp hnp

example {P Q: Prop} (h: ¬(P ∨ Q)): ¬P ∧ ¬Q := sorry

example {P Q R: Prop}: ((P ∧ Q) → R) → (P → (Q → R))
  | h => fun hp hq => h ⟨hp, hq⟩

example {P Q R: Prop}: (P → (Q → R)) → ((P ∧ Q) → R)
  | h => fun ⟨hp, hq⟩ => h hp hq

/-
## Proof Irrelevance (Advanced)
-/

def propExt: Prop := ∀ P Q: Prop, (P ↔ Q) → P = Q

example: propExt → ∀ P Q: Prop, (P ∨ Q) = (Q ∨ P)
  | h, P, Q =>
    have h₁: P ∨ Q ↔ Q ∨ P :=
      have mp: P ∨ Q → Q ∨ P
        | .inl hp => .inr hp
        | .inr hq => .inl hq
      have mpr: Q ∨ P → P ∨ Q
        | .inl hq => .inr hq
        | .inr hp => .inl hp
      ⟨mp, mpr⟩
    h (P ∨ Q) (Q ∨ P) h₁

example: propExt → ∀ P: Prop, P → True = P
  | h₁, P, hp =>
    have h₂: True ↔ P :=
      have mp: True → P
        | _ => hp
      have mpr: P → True
        | _ => True.intro
      ⟨mp, mpr⟩
    h₁ True P h₂

def proofIrrelevance: Prop := ∀ P: Prop, ∀ p₁ p₂: P, p₁ = p₂

-- example: propExt → proofIrrelevance
--   | h =>
--     fun P p₁ p₂ =>
--       have h₁: p₁ ↔ p₂ :=
--         have mp: p₁ → p₂
--           | p₁ => p₂
--         have mpr: p₂ → p₁
--           | p₂ => p₁
--         ⟨mp, mpr⟩
--       h P P h₁
