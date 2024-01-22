/-
# Inductive Propositions
-/

import «SoftwareFoundations».«LogicalFoundations».«Logic»

/-
## Inductively Defined Propositions
-/

/-
### Example: The Collatz Conjecture
-/

def div2: Nat → Nat
  | 0 => 0
  | .succ .zero => 0
  | .succ (.succ n) => (div2 n).succ

def f (n: Nat): Nat :=
  if n.isEven
  then div2 n
  else (3 * n) + 1

inductive CollatzHoldsFor: Nat → Prop where
  | done: CollatzHoldsFor 1
  | more (n: Nat): CollatzHoldsFor (f n) → CollatzHoldsFor n

example: CollatzHoldsFor 12 := by
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.more; simp [f, div2]
  apply CollatzHoldsFor.done

example (n: Nat): CollatzHoldsFor n := by sorry

/-
### Example: Ordering
-/

inductive Leq: Nat → Nat → Prop where
  | eq (n: Nat): Leq n n
  | less (n₁ n₂: Nat) (h: Leq n₁ n₂): Leq n₁ n₂.succ

example: Leq 3 5 :=
  (Leq.less 3 4 (Leq.less 3 3 (Leq.eq 3)))

example: Leq 3 5 :=
  Leq.eq 3
    |> Leq.less 3 3
    |> Leq.less 3 4

example: Leq 3 5 := by
  apply Leq.less
  apply Leq.less
  apply Leq.eq

/-
### Example: Transitive Closure
-/

inductive ClosTrans (R: α → α → Prop): α → α → Prop where
  | step (x₁ x₂: α): R x₁ x₂ → ClosTrans R x₁ x₂
  | trans (x₁ x₂ x₃: α): ClosTrans R x₁ x₂ → ClosTrans R x₂ x₃ → ClosTrans R x₁ x₃

inductive Person: Type where
  | sage
  | cleo
  | ridley
  | moss

inductive ParentOf: Person → Person → Prop :=
  | sc: ParentOf .sage .cleo
  | sr: ParentOf .sage .ridley
  | cm: ParentOf .cleo .moss

def Person.ancestorOf: Person → Person → Prop := ClosTrans ParentOf

example: Person.sage.ancestorOf .moss := by
  unfold Person.ancestorOf
  apply ClosTrans.trans _ .cleo
  apply ClosTrans.step
  apply ParentOf.sc
  apply ClosTrans.step
  apply ParentOf.cm

/-
### Example: Permutations
-/

inductive Perm₃: List α → List α → Prop where
  | swap12 (x₁ x₂ x₃: α): Perm₃ [x₁, x₂, x₃] [x₂, x₁, x₃]
  | swap23 (x₁ x₂ x₃: α): Perm₃ [x₁, x₂, x₃] [x₁, x₃, x₂]
  | trans (l₁ l₂ l₃: List α): Perm₃ l₁ l₂ → Perm₃ l₂ l₃ → Perm₃ l₁ l₃

example: Perm₃ [1, 2, 3] [2, 3, 1] :=
  Perm₃.trans _ _ _
    (Perm₃.swap12 1 2 3)
    (Perm₃.swap23 2 1 3)

example: Perm₃ [1, 2, 3] [2, 3, 1] := by
  apply Perm₃.trans _ _ _
  · apply Perm₃.swap12 1 2 3
  · apply Perm₃.swap23 2 1 3

/-
### Example: Evenness (yet again)
-/

inductive Even: Nat → Prop where
  | zero: Even 0
  | succSucc (n: Nat) (h: Even n): Even n.succ.succ

example: Even 4 := by
  apply Even.succSucc
  apply Even.succSucc
  apply Even.zero

example: Even 4 :=
  Even.succSucc 2 (Even.succSucc 0 Even.zero)

example: Even 4 := by
  apply Even.succSucc 2 (Even.succSucc 0 Even.zero)

example (n: Nat) (h: Even n): Even (n + 4) :=
  Even.succSucc _ (Even.succSucc n h)

example (n: Nat) (h: Even n): Even (4 + n) := by
  rw [Nat.add_comm]
  apply Even.succSucc _ (Even.succSucc n h)

example (n: Nat): Even n.double := by
  induction n with
    | zero => apply Even.zero
    | succ n ih =>
      apply Even.succSucc
      assumption

theorem indEvenDouble: ∀ n: Nat, Even n.double
  | .zero => Even.zero
  | .succ n => Even.succSucc n.double (indEvenDouble n)

/-
## Using Evidence in Proofs
-/

/-
### Inversion on Evidence
-/

example (n₁: Nat): Even n₁ → n₁ = 0 ∨ (∃ n₂: Nat, n₁ = n₂.succ.succ ∧ Even n₂)
  | .zero => .inl rfl
  | .succSucc n₂ he => .inr ⟨n₂, ⟨rfl, he⟩⟩

theorem evInversion (n₁: Nat) (h: Even n₁): n₁ = 0 ∨ (∃ n₂: Nat, n₁ = n₂.succ.succ ∧ Even n₂) := by
  cases h with
    | zero =>
      apply Or.inl
      rfl
    | succSucc n h =>
      apply Or.inr
      exists n

theorem evenSuccSuccEven (n: Nat): Even n.succ.succ → Even n
  | .succSucc _ h => h

example (n: Nat) (h: Even n.succ.succ): Even n := by
  cases h; assumption

example: ¬(Even 1) := by
  intro h
  contradiction

example (n: Nat): Even n.succ.succ.succ.succ → Even n
  | .succSucc _ (.succSucc _ h) => h

example (n: Nat) (h: Even n.succ.succ.succ.succ): Even n := by
  cases h with
    | succSucc _ h =>
      cases h with
        | succSucc _ h => assumption

example (h: Even 5): 2 + 2 = 9 := by
  contradiction

example (n₁ n₂ n₃: Nat) (h: [n₁, n₂] = [n₃, n₃]): [n₁] = [n₂] := by
  simp at h
  cases h with
    | intro l r => rw [l, r]

example (n: Nat) (h: n.succ = 0): 2 + 2 = 5 := by
  contradiction

theorem evenEvenProp (n₁: Nat) (h₁: Even n₁): Nat.evenProp n₁ := by
  induction h₁ with
    | zero => exists 0
    | succSucc n₂ _ ih =>
      unfold Nat.evenProp at ih
      cases ih with
        | intro w h₃ =>
          rw [h₃]
          unfold Nat.evenProp
          exists w.succ

theorem evenEvenPropIff (n₁: Nat): Even n₁ ↔ Nat.evenProp n₁ := by
  apply Iff.intro
  · intro h
    apply evenEvenProp
    assumption
  · intro h
    unfold Nat.evenProp at h
    cases h with
      | intro w h =>
        rw [h]
        apply indEvenDouble

theorem evenPlusEven (n₁ n₂: Nat) (h₁: Even n₁) (h₂: Even n₂): Even (n₁ + n₂) := by
  induction h₁ with
    | zero =>
      cases n₂ with
        | zero => apply Even.zero
        | succ n₂ =>
          simp
          exact h₂
    | succSucc n₁ h₁ ih₁ =>
      cases n₂ with
        | zero =>
          rw [Nat.add_zero]
          apply Even.succSucc
          exact h₁
        | succ n₂ =>
          rw [Nat.succ_add, ← Nat.succ_eq_add_one, Nat.succ_add]
          apply Even.succSucc
          exact ih₁

inductive EvenSum: Nat → Prop where
  | zero: EvenSum 0
  | two: EvenSum 2
  | sum (n₁ n₂: Nat) (h₁: EvenSum n₁) (h₂: EvenSum n₂): EvenSum (n₁ + n₂)

example (n: Nat): Even n ↔ EvenSum n :=
  ⟨mp n, mpr n⟩
  where
    mp (n: Nat): Even n → EvenSum n
      | .zero => .zero
      | .succSucc k h => .sum k 2 (mp k h) .two
    mpr (n: Nat): EvenSum n → Even n
      | .zero => .zero
      | .two => .succSucc 0 .zero
      | .sum n₁ n₂ h₁ h₂ => evenPlusEven n₁ n₂ (mpr n₁ h₁) (mpr n₂ h₂)

example (n: Nat): Even n ↔ EvenSum n := by
  apply Iff.intro
  · intro h
    induction h with
      | zero => apply EvenSum.zero
      | succSucc n _ ih =>
        apply EvenSum.sum n 2
        · assumption
        · apply EvenSum.two
  · intro h
    induction h with
      | zero => apply Even.zero
      | two =>
        apply Even.succSucc
        apply Even.zero
      | sum n₁ n₂ _ _ ih₁ ih₂ =>
        apply evenPlusEven
        · assumption
        · assumption

theorem evenSum (n₁ n₂: Nat) (h₁: Even (n₁ + n₂)) (h₂: Even n₁): Even n₂ := by
  induction h₂ with
    | zero =>
      simp [Nat.zero_add] at h₁
      assumption
    | succSucc n _ ih =>
      rw [Nat.succ_add, Nat.succ_add] at h₁
      have h₂: Even (n + n₂) := evenSuccSuccEven (n + n₂) h₁
      apply ih h₂

example (n₁ n₂ n₃: Nat) (h₁: Even (n₁ + n₂)) (h₂: Even (n₁ + n₃)): Even (n₂ + n₃) := by
  rw [Nat.add_comm] at h₁
  rw [Nat.add_comm] at h₂
  have h₃: Even ((n₁ + n₂) + (n₁ + n₃)) := by
    rw [Nat.add_comm n₁ n₂]
    rw [Nat.add_comm] at h₂
    exact evenPlusEven (n₂ + n₁) (n₁ + n₃) h₁ h₂
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_right_comm] at h₃
  sorry

/-
## Inductive Relations
-/

namespace Playground
  example: Leq 3 3 := by
    apply Leq.eq

  example: Leq 3 6 := by
    apply Leq.less
    apply Leq.less
    apply Leq.less
    apply Leq.eq

  example (h: Leq 2 1): 2 + 2 = 5 := by
    contradiction

  def lt (n₁ n₂: Nat): Prop := Leq n₁.succ n₂
end Playground

inductive TotalRelation: Nat → Nat → Prop where
  | related (n₁ n₂: Nat): TotalRelation n₁ n₂

example (n₁ n₂: Nat): TotalRelation n₁ n₂ := by
  apply TotalRelation.related

namespace Ignored
  inductive EmptyRelation: Nat → Nat → Prop

  example (n₁ n₂: Nat): ¬(EmptyRelation n₁ n₂) := by
    unfold Not
    intro h
    contradiction
end Ignored

theorem Leq.trans (n₁ n₂ n₃: Nat) (h₁: Leq n₁ n₂) (h₂: Leq n₂ n₃): Leq n₁ n₃ := by
  induction h₂ with
    | eq => exact h₁
    | less n _ ih =>
      apply Leq.less
      exact ih

example {n₁ n₂ n₃: Nat} (h₁: Leq n₁ n₂) (h₂: Leq n₂ n₃): Leq n₁ n₃ := by
  induction h₁ with
    | eq => exact h₂
    | less n h ih =>
      have h₃: Leq n n₃ :=
        -- _example
        sorry
      apply ih h₃

example {n₁ n₂ n₃: Nat}: Leq n₁ n₂ → Leq n₂ n₃ → Leq n₁ n₃
  | h₁, .eq _ => h₁
  | h₁, .less _ n h₂ => sorry

example {n₁ n₂ n₃: Nat}: Leq n₁ n₂ → Leq n₂ n₃ → Leq n₁ n₃
  | h₁, .eq _ => h₁
  | h₁, .less _ n h₂ =>
    have h₃: Leq n₁ n := _example h₁ h₂
    Leq.less n₁ n h₃

theorem Leq.zeroLeqSucc (n: Nat): Leq 0 n := by
  induction n with
    | zero => apply Leq.eq
    | succ n ih =>
      apply Leq.less 0 n
      assumption

example: ∀ n: Nat, Leq 0 n
  | .zero => Leq.eq 0
  | .succ n => Leq.less 0 n (_example n)

theorem Leq.leqSucc {n₁ n₂: Nat} (h: Leq n₁ n₂): Leq n₁.succ n₂.succ := by
  induction h with
    | eq =>
      apply Leq.eq
    | less _ _ ih =>
      apply Leq.less
      apply ih

-- example {n₁ n₂: Nat}: Leq n₁ n₂ → Leq n₁.succ n₂.succ
--   | .eq _ => sorry
--   | .less _ n₃ h => _example (Leq.less n₁ n₃ h)

theorem Leq.succLeq (n₁ n₂: Nat) (h: Leq n₁.succ n₂.succ): Leq n₁ n₂ := by
  cases h with
    | eq =>
      apply Leq.eq
    | less n h => sorry

theorem Leq.ltGeCases (n₁ n₂: Nat): Playground.lt n₁ n₂ ∨ Leq n₁ n₂ := by
  unfold Playground.lt
  induction n₁ with
    | zero =>
      cases n₂ with
        | zero =>
          apply Or.inr
          apply Leq.eq
        | succ n₂ =>
          apply Or.inr
          apply zeroLeqSucc
    | succ n₁ ih => sorry

theorem Leq.lePlusL (n₁ n₂: Nat): Leq n₁ (n₁ + n₂) := by
  induction n₁ with
    | zero =>
      simp
      apply Leq.zeroLeqSucc
    | succ n₁ ih =>
      rw [Nat.succ_add]
      apply Leq.leqSucc
      exact ih

example: ∀ n₁ n₂: Nat, Leq n₁ (n₁ + n₂)
  | .zero, n₂ => sorry
  | .succ n₁, n₂ =>
    have h₁: n₁.succ + n₂ = (n₁ + n₂).succ := Nat.succ_add n₁ n₂
    have h₂: Leq n₁.succ (n₁ + n₂).succ    := Leq.leqSucc (_example n₁ n₂)
    have h₃: Leq n₁.succ (n₁.succ + n₂) = Leq n₁.succ (n₁ + n₂).succ :=
      calc Leq n₁.succ (n₁.succ + n₂)
        _ = Leq n₁.succ (n₁ + n₂).succ := by rw [h₁]
    sorry

theorem Leq.plusLeq (n₁ n₂ n₃: Nat) (h: Leq (n₁ + n₂) n₃): Leq n₁ n₃ ∨ Leq n₂ n₃ := by
  sorry

theorem Leq.addLeCases (n₁ n₂ n₃ n₄: Nat) (h: Leq (n₁ + n₂) (n₃ + n₄)): Leq n₁ n₃ ∨ Leq n₂ n₄ := by
  induction n₁ with
    | zero =>
      simp
      apply Or.inl
      apply Leq.zeroLeqSucc
    | succ n₁ ih =>
      rw [Nat.succ_add] at h
      sorry

theorem Leq.plusLeqCompatLeft (n₁ n₂ n₃: Nat) (h: Leq n₁ n₂): Leq (n₃ + n₁) (n₃ + n₂) := by
  induction n₃ with
    | zero =>
      simp
      assumption
    | succ n₃ ih =>
      simp [Nat.succ_add]
      apply Leq.leqSucc
      apply ih

example: ∀ n₁ n₂ n₃: Nat, Leq n₁ n₂ → Leq (n₃ + n₁) (n₃ + n₂)
  | n₁, n₂, .zero, h => sorry
  | n₁, n₂, .succ n₃, h => sorry

theorem Leq.plusLeqCompatRight (n₁ n₂ n₃: Nat) (h: Leq n₁ n₂): Leq (n₁ + n₃) (n₂ + n₃) := by
  induction n₃ with
    | zero =>
      simp
      assumption
    | succ n₃ ih =>
      simp [Nat.add_succ]
      apply Leq.leqSucc
      apply ih

example: ∀ n₁ n₂ n₃: Nat, Leq n₁ n₂ →  Leq (n₁ + n₃) (n₂ + n₃)
  | n₁, .zero, n₃, h => sorry
  | n₁, .succ n₂, n₃, h => sorry

theorem Leq.plusTrans (n₁ n₂ n₃: Nat) (h: Leq n₁ n₂): Leq n₁ (n₂ + n₃) := by
  induction n₂ with
    | zero =>
      simp_all
      cases n₃ with
        | zero => simp_all
        | succ n₃ =>
          have h₂: n₁ = 0 := sorry
          rw [h₂]
          apply Leq.zeroLeqSucc
    | succ n₂ ih =>
      simp [Nat.succ_add]
      apply Leq.less
      apply ih
      sorry

theorem Leq.ltLeq (n₁ n₂: Nat) (h: Playground.lt n₁ n₂): Leq n₁ n₂ := by
  unfold Playground.lt at h
  sorry

theorem Leq.plusLt (n₁ n₂ n₃: Nat) (h: Playground.lt (n₁ + n₂) n₃): Playground.lt n₁ n₃ ∧ Playground.lt n₂ n₃ := by
  induction n₃ with
    | zero =>
      simp
      contradiction
    | succ n₃ ih =>
      apply And.intro
      · apply Leq.leqSucc
        sorry
      · apply Leq.leqSucc
        sorry

theorem lessEqComplete (n₁ n₂: Nat) (h: (n₁.less_eq n₂) = true): Leq n₁ n₂ := by
  sorry

theorem lessEqCorrect (n₁ n₂: Nat) (h: Leq n₁ n₂): n₁.less_eq n₂ = true := by
  induction n₂ with
    | zero =>
      simp_all
      cases n₁ with
        | zero => simp
        | succ n₁ => contradiction
    | succ n₂ ih =>
      cases n₁ with
        | zero =>
          simp_all
          sorry
        | succ n₁ =>
          sorry

theorem lessEqIff (n₁ n₂: Nat): n₁.less_eq n₂ ↔ Leq n₁ n₂ := by
  apply Iff.intro
  · intro h
    sorry
  · intro h
    sorry

theorem lessEqTrueTrans (n₁ n₂ n₃: Nat) (h₁: n₁.less_eq n₂ = true) (h₂: n₂.less_eq n₃ = true): n₁.less_eq n₃ = true := by
  sorry

namespace R
  inductive R: Nat → Nat → Nat → Prop where
    | c₁: R 0 0 0
    | c₂ (n₁ n₂ n₃: Nat) (h: R n₁ n₂ n₃): R n₁.succ n₂ n₃.succ
    | c₃ (n₁ n₂ n₃: Nat) (h: R n₁ n₂ n₃): R n₁ n₂.succ n₃.succ
    | c₄ (n₁ n₂ n₃: Nat) (h: R n₁.succ n₂.succ n₃.succ.succ): R n₁ n₂ n₃
    | c₅ (n₁ n₂ n₃: Nat) (h: R n₁ n₂ n₃): R n₂ n₁ n₃

  example: R 1 1 2 := by
    apply R.c₂
    apply R.c₃
    apply R.c₁

  -- example: R 2 2 6 := by
  --   apply R.c₂
  --   apply R.c₃
  --   apply R.c₄
  --   apply R.c₂
  --   apply R.c₃
  --   apply R.c₄

  def fR (n₁ n₂: Nat): Nat := n₁ + n₂

  theorem fREqR (n₁ n₂ n₃: Nat): R n₁ n₂ n₃ ↔ fR n₁ n₂ = n₃ := by
    unfold fR
    apply Iff.intro
    · intro h
      induction h with
        | c₁ => rfl
        | c₂ n₁ n₂ n₃ h ih =>
          rw [Nat.succ_add]
          sorry
        | c₃ n₁ n₂ n₃ h ih =>
          rw [Nat.add_succ]
          sorry
        | c₄ n₁ n₂ n₃ h ih =>
          apply succInj
          apply succInj
          rw [← Nat.add_succ n₁ n₂, ← Nat.succ_add n₁ n₂.succ]
          exact ih
        | c₅ n₁ n₂ n₃ h ih =>
          rw [Nat.add_comm]
          exact ih
    · intro h
      induction n₁ with
        | zero =>
          rw [Nat.zero_add] at h
          simp
          sorry
        | succ n ih =>
          sorry
end R

inductive Subsequence: List Nat → List Nat → Prop where
  | nil: Subsequence [] []
  | found: Subsequence [] _
  | notFound: Subsequence _ []

theorem subseqRefl (l: List Nat): Subsequence l l := by
  induction l with
    | nil =>
      exact Subsequence.nil
    | cons hd tl ih => sorry

theorem subseqApp (l₁ l₂ l₃: List Nat) (h: Subsequence l₁ l₂): Subsequence l₁ (l₂ ++ l₃) := by
  sorry

theorem subseqTrans (l₁ l₂ l₃: List Nat) (h₁: Subsequence l₁ l₂) (h₂: Subsequence l₂ l₃): Subsequence l₁ l₂ := by
  sorry

inductive R: Nat → List Nat → Prop where
  | c₁: R 0 []
  | c₂ (n: Nat) (l: List Nat) (h: R n l): R n.succ (n :: l)
  | c₃ (n: Nat) (l: List Nat) (h: R n.succ l): R n l

example: R 2 [1, 0] := by
  apply R.c₂
  apply R.c₂
  apply R.c₁

/-
## A Digression on Notation
-/

inductive Bin₁: Type where
  | zero
  | b₀ (n: Bin₁)
  | b₁ (n: Bin₁)

inductive Bin₂: Type where
  | zero: Bin₂
  | b₀ (n: Bin₂): Bin₂
  | b₁ (n: Bin₂): Bin₂

inductive Bin₃: Type where
  | zero: Bin₃
  | b₀: Bin₃ → Bin₃
  | b₁: Bin₃ → Bin₃

/-
## Case Study: Regular Expressions
-/

inductive RegExp (α: Type): Type where
  | emptySet
  | emptyString
  | char (ch: α)
  | app (re₁ re₂: RegExp α)
  | union (re₁ re₂: RegExp α)
  | star (re: RegExp α)

inductive Match: List α → RegExp α → Prop where
  | empty: Match [] .emptyString
  | char (x: α): Match [x] (.char x)
  | app (s₁: List α) (re₁: RegExp α) (s₂: List α) (re₂: RegExp α) (h₁: Match s₁ re₁) (h₂: Match s₂ re₂): Match (s₁ ++ s₂) (.app re₁ re₂)
  | unionLeft (s₁: List α) (re₁ re₂: RegExp α) (h: Match s₁ re₁): Match s₁ (.union re₁ re₂)
  | unionRight (s₁: List α) (re₁ re₂: RegExp α) (h: Match s₁ re₂): Match s₁ (.union re₁ re₂)
  | star0 (re: RegExp α): Match [] (.star re)
  | starApp (s₁ s₂: List α) (re: RegExp α) (h₁: Match s₁ re) (h₂: Match s₂ (.star re)): Match (s₁ ++ s₂) (.star re)

example: Match [1] (.char 1) := by
  apply Match.char

example: Match [1, 2] (.app (.char 1) (.char 2)) := by
  apply Match.app [1] <;> apply Match.char

example: ¬(Match [1, 2] (.char 1)) := by
  unfold Not
  intro h
  sorry

def RegExp.ofList: List α → RegExp α
  | [] => RegExp.emptyString
  | hd :: tl => RegExp.app (.char hd) (RegExp.ofList tl)

example: Match [1, 2, 3] (RegExp.ofList [1, 2, 3]) := by
  apply Match.app [1]
  · apply Match.char
  · apply Match.app [2]
    · apply Match.char
    · apply Match.app [3]
      · apply Match.char
      · apply Match.empty

theorem matchStar (s: List α) (re: RegExp α) (h: Match s re): Match s (.star re) := by
  have List.nil_append (l: List α): [] ++ l = l := by
    cases l <;> rfl
  sorry

theorem emptyIsEmpty (s: List α): ¬(Match s .emptySet) := by
  intro h
  contradiction

theorem matchUnion (s: List α) (re₁ re₂: RegExp α) (h: Match s re₁ ∨ Match s re₂): Match s (.union re₁ re₂) := by
  cases h with
    | inl h =>
      apply Match.unionLeft
      assumption
    | inr h =>
      apply Match.unionRight
      assumption

theorem foldStar (ss: List (List α)) (re: RegExp α) (h: ∀ s: List α, ss.mem s → Match s re): Match (ss.foldr app []) (.star re) := by
  sorry

def RegExp.allChars: RegExp α → List α
  | .emptySet => []
  | .emptyString => []
  | .char x => [x]
  | .app re₁ re₂ => re₁.allChars ++ re₂.allChars
  | .union re₁ re₂ => re₁.allChars ++ re₂.allChars
  | .star re => re.allChars

theorem memRegExpMatch (s: List α) (re: RegExp α) (x: α) (h₁: Match s re) (h₂: s.mem x): re.allChars.mem x := by
  induction h₁ with
    | empty => contradiction
    | char _ => assumption
    | app s₁ re₁ s₂ re₂ h₃ h₄ ih₃ ih₄ =>
      unfold RegExp.allChars
      sorry
    | unionLeft s₁ re₁ re₂ h ih =>
      simp_all
      sorry
    | unionRight s₁ re₁ re₂ h ih =>
      simp_all
      sorry
    | star0 re =>
      unfold List.mem at h₂
      contradiction
    | starApp s₁ s₂ re h₃ h₄ ih₃ ih₄ =>
      sorry

def RegExp.notEmpty: RegExp α → Bool
  | .emptySet => false
  | .emptyString => false
  | .char x => true
  | .app re₁ re₂ => re₁.notEmpty || re₂.notEmpty
  | .union re₁ re₂ => re₁.notEmpty || re₂.notEmpty
  | .star re => re.notEmpty

theorem reNotEmptyCorrect (re: RegExp α): (∃ s: List α, Match s re) ↔ re.notEmpty = true := by
  apply Iff.intro
  · intro h
    sorry
  · intro h
    sorry

theorem starApp (s₁ s₂: List α) (re: RegExp α) (h₁: Match s₁ (.star re)) (h₂: Match s₂ (.star re)): Match (s₁ ++ s₂) (.star re) := by
  generalize h₃: RegExp.star re = x
  sorry

theorem starApp' (s₁: List α) (re: RegExp α) (h₁: Match s re) (h₂: ∃ ss: List (List α), s₁ = ss.foldr app [] ∧ ∀ s₂: List α, ss.mem s₂): Match s₂ re := by
  induction h₂ with
    | intro w h =>
      cases h with
        | intro l r =>
          sorry

def List.napp (l: List α): Nat → List α
  | .zero => []
  | .succ n => l ++ napp l n

def RegExp.pumpingConstant: RegExp α → Nat
  | .emptySet => 1
  | .emptyString => 1
  | .char _ => 2
  | .app re₁ re₂ => pumpingConstant re₁ + pumpingConstant re₂
  | .union re₁ re₂ => pumpingConstant re₁ + pumpingConstant re₂
  | .star re => pumpingConstant re

namespace Pumping
  theorem RegExp.pumpingConstantGe1 (re: RegExp α): re.pumpingConstant ≥ 1 := by
    unfold RegExp.pumpingConstant
    cases re with
      | emptySet => simp
      | emptyString => simp
      | char _ => simp
      | app re₁ re₂ => sorry
      | union re₁ re₂ => sorry
      | star re => sorry
  theorem RegExp.pumpingConstantZeroFalse (re: RegExp α) (h: re.pumpingConstant = 0): False := by
    sorry

  theorem nappPlus (n₁ n₂: Nat) (l: List α): l.napp (n₁ + n₂) = l.napp n₁ ++ l.napp n₂ := by
    induction n₁ with
      | zero => simp [List.napp, List.nil_append]
      | succ n ihₙ => simp_all [Nat.succ_add, List.napp, List.append_assoc]

  theorem nappStar (n: Nat) (s₁ s₂: List α) (re: RegExp α) (h₁: Match s₁ re) (h₂: Match s₂ (.star re)): Match ((s₁ ++ s₂).napp n) (.star re) := by
    induction n with
      | zero =>
        simp [List.napp]
        sorry
      | succ n ihₙ =>
        sorry

  theorem weakPumping (re: RegExp α) (s: List α) (h₁: Match s re) (h₂: re.pumpingConstant ≤ s.length): ∃ s₁ s₂ s₃: List α, s = s₁ ++ s₂ ++ s₃ ∧ s ≠ [] ∧ ∀ n: Nat, Match (s₁ ++ s₂.napp n ++ s₃) re := by
    induction h₁ with
      | empty =>
        simp_all
        contradiction
      | char x =>
        simp_all
        sorry
      | app s₁ re₁ s₂ re₂ h₁ h₂ ih₁ ih₂ =>
        simp_all
        sorry
      | unionLeft s re₁ re₂ h ih =>
        simp_all
        sorry
      | unionRight s re₁ re₂ h ih =>
        simp_all
        sorry
      | star0 re =>
        simp_all
        sorry
      | starApp s₁ s₂ re₂ h₁ h₂ ih₁ ih₂ =>
        simp_all
        sorry

  theorem pumping (re: RegExp α) (s: List α) (h₁: Match s re) (h₂: re.pumpingConstant ≤ s.length): ∃ s₁ s₂ s₃: List α, s = s₁ ++ s₂ ++ s₃ ∧ s ≠ [] ∧ s₁.length + s₂.length ≤ re.pumpingConstant ∧ ∀ n: Nat, Match (s₁ ++ s₂.napp n ++ s₃) re := by
    sorry
end Pumping

/-
## Case Study: Improving Reflection
-/



/-
## Additional Exercises
-/
