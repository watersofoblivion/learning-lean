/-
# More Basic Tactics
-/

import «SoftwareFoundations».«LogicalFoundations».«Poly»

/-
## The `apply` Tactic
-/

theorem silly (n₁ n₂: Nat) (h: n₁ = n₂): n₁ = n₂ := by
  apply h

theorem silly2 (n₁ n₂ n₃ n₄: Nat) (h₁: n₁ = n₂) (h₂: n₁ = n₂ → (PolyList.cons n₁ (.cons n₃ .nil)) = (PolyList.cons n₂ (.cons n₄ .nil))): (PolyList.cons n₁ (.cons n₃ .nil)) = (PolyList.cons n₂ (.cons n₄ .nil)) := by
  apply h₂
  apply h₁

theorem silly2a (n₁ n₂: Nat) (h₁: (⟨n₁, n₁⟩: PolyProd Nat Nat) = ⟨n₂, n₂⟩) (h₂: ∀ (n₃ n₄: Nat), (⟨n₃, n₃⟩: PolyProd Nat Nat) = ⟨n₄, n₄⟩ → (PolyList.cons n₃ .nil) = .cons n₄ .nil): (PolyList.cons n₁ .nil) = .cons n₂ .nil := by
  apply h₂
  apply h₁

theorem sillyEx (n: Nat) (h₁: ∀ (n₁: Nat), n₁.isEven → ¬n₁.succ.isEven) (h₂: ∀ (n₂: Nat), ¬n₂.isEven → n₂.isOdd) (h₃: n.isEven): n.succ.isOdd := by
  apply h₂
  apply h₁
  apply h₃

theorem silly3 (n₁ n₂: Nat) (h: n₁ = n₂): n₂ = n₁ := by
  rw [Eq.symm h]

/-
#### Exercises
-/

theorem PolyList.revExercise (l₁ l₂: PolyList Nat) (h: l₁ = l₂.rev): l₂ = l₁.rev := by
  rw [h, PolyList.revInvolute]

/-
## The `apply with` Tactic
-/

example (n₁ n₂ n₃ n₄ n₅ n₆: Nat) (h₁: PolyList.cons n₁ (.cons n₂ .nil) = .cons n₃ (.cons n₄ .nil)) (h₂: (PolyList.cons n₃ (.cons n₄ .nil)) = .cons n₅ (.cons n₆ .nil)): (PolyList.cons n₁ (.cons n₂ .nil)) = .cons n₅ (.cons n₆ .nil) := by
  rw [h₁, h₂]

theorem eqTrans {α: Type} (x₁ x₂ x₃: α) (h₁: x₁ = x₂) (h₂: x₂ = x₃): x₁ = x₃ := by
  rw [h₁, h₂]

example (n₁ n₂ n₃ n₄ n₅ n₆: Nat) (h₁: PolyList.cons n₁ (.cons n₂ .nil) = .cons n₃ (.cons n₄ .nil)) (h₂: (PolyList.cons n₃ (.cons n₄ .nil)) = .cons n₅ (.cons n₆ .nil)): (PolyList.cons n₁ (.cons n₂ .nil)) = .cons n₅ (.cons n₆ .nil) := by
  apply eqTrans _ (PolyList.cons n₃ (.cons n₄ .nil)) _
  apply h₁
  apply h₂

/-
#### Exercises
-/

example (n₁ n₂ n₃ n₄: Nat) (h₁: n₂ = n₃.minusTwo) (h₂: n₁ + n₄ = n₂): n₁ + n₄ = n₃.minusTwo := by
  apply Eq.trans h₂ h₁

/-
## The `injection` and `discriminate` (`contradiction`) Tactics
-/

theorem Nat.succInj (n₁ n₂: Nat) (h₁: n₁.succ = n₂.succ): n₁ = n₂ := by
  have h₂: n₁ = n₁.succ.pred := by rw [Nat.pred_succ]
  rw [h₂, h₁]
  simp


theorem succInjTactic (n₁ n₂: Nat) (h: n₁.succ = n₂.succ): n₁ = n₂ := by
  injection h

theorem injExample (n₁ n₂ n₃: Nat) (h: (PolyList.cons n₁ (.cons n₂ .nil)) = (PolyList.cons n₃ (.cons n₃ .nil))): n₁ = n₂ := by
  injection h with h₁ h₂
  rw [h₁]
  injection h₂ with h₃ h₄
  rw [Eq.symm h₃]

theorem contraditionExample₁ (n₁ n₂: Nat) (h: false = true): n₁ = n₂ := by
  contradiction

theorem contraditionExample₂ (n: Nat) (h: n.succ = 0): 2 + 2 = 5 := by
  contradiction

/-
#### Exercises
-/

theorem injExercise (x₁ x₂ x₃: α) (l₁ l₂: PolyList α) (h₁: PolyList.cons x₁ (.cons x₂ l₁) = .cons x₃ l₂) (h₂: l₂ = .cons x₃ l₁): x₁ = x₂ := by
  injection h₁ with h₃ h₄
  rw [h₃]
  rw [h₂] at h₄
  injection h₄ with h₅ h₆
  rw [Eq.symm h₅]

theorem contraExcercise (x₁ x₂ x₃: α) (l: PolyList α) (h: PolyList.cons x₁ (.cons x₂ l) = .nil): x₁ = x₃ := by
  contradiction

theorem Nat.beqZeroLeft (n: Nat) (h: Nat.zero.eq n = true): n = 0 := by
  cases n with
    | zero => rfl
    | succ n => contradiction

theorem fEqual (f: α → β) (x₁ x₂: α) (h: x₁ = x₂): f x₁ = f x₂ := by
  rw [h]

theorem Nat.eqImpliesSuccEq (n₁ n₂: Nat) (h: n₁ = n₂): n₁.succ = n₂.succ := by
  rw [h]

-- No eqivalent of f_equal?

/-
## Using Tactics on Hypotheses
-/

theorem Nat.succInj₂ (n₁ n₂: Nat) (b: Bool) (h: n₁.succ.eq n₂.succ = b): n₁.eq n₂ = b := by
  simp [Nat.eq] at h
  exact h

theorem silly4 (n₁ n₂ n₃ n₄: Nat) (h₁: n₁ = n₂ → n₃ = n₄) (h₂: n₂ = n₁): n₄ = n₃ := by
  simp [Eq.symm h₂] at h₁
  rw [Eq.symm h₁]

/-
## Specializing Hypotheses
-/

theorem specializeExample (n₁: Nat) (h: ∀ (n₂: Nat), n₁ * n₂ = 0): n₁ = 0 := by
  specialize h 1
  simp at h
  exact h

-- Lean cannot specialize non-local theorems, unlike Coq

/-
## Varying the Induction Hypothesis
-/

theorem Nat.doubleInjective (n₁ n₂: Nat) (h: Nat.double n₁ = Nat.double n₂): n₁ = n₂ := by
  revert n₂ h
  induction n₁ with
    | zero =>
      intro n₂ h
      cases n₂ with
        | zero => rfl
        | succ n₂ => contradiction
    | succ n₁ ihn₁ =>
      intro n₂ h
      cases n₂ with
        | zero => contradiction
        | succ n₂ =>
          apply fEqual
          apply ihn₁ n₂
          injection h with h₁
          -- apply h₁
          sorry

theorem Bool.eqTrue (b₁ b₂: Bool) (h: (b₁ == b₂) = true): b₁ == b₂ := by
  rw [Bool.beq_to_eq] at h
  simp
  sorry

theorem Nat.plusNNInjective (n₁ n₂: Nat) (h: n₁ + n₁ = n₂ + n₂): n₁ = n₂ := by
  revert n₂ h
  induction n₁ with
    | zero =>
      intro n₂ h
      cases n₂ with
        | zero => simp
        | succ n₂ => contradiction
    | succ n₁ ihn₁ =>
      intro n₂ h
      cases n₂ with
        | zero => contradiction
        | succ n₂ =>
          apply fEqual
          simp [Nat.add_succ] at h
          sorry

theorem Nat.doubleInjective₂ (n₁ n₂: Nat) (h: Nat.double n₁ = Nat.double n₂): n₁ = n₂ := by
  revert n₁
  induction n₂ with
    | zero =>
      intro n₁ h
      cases n₁ with
        | zero => rfl
        | succ n₁ => contradiction
    | succ n₂ ihn₂ =>
      intro n₁ h
      cases n₁ with
        | zero => contradiction
        | succ n₁ =>
          apply fEqual
          apply ihn₂
          injection h with h₁
          sorry

theorem Nat.nthErrAfterLast (n: Nat) (α: Type) (l: PolyList α) (h: l.length = n): l.nthOpt n = PolyOption.none := by
  induction l with
    | nil => simp [PolyList.length, PolyList.nthOpt]
    | cons hd tl ihₗ =>
      rw [PolyList.length] at h
      sorry

/-
## Unfolding definitions
-/

def Nat.square (n: Nat): Nat := n * n

theorem squareMult (n₁ n₂: Nat): (n₁ * n₂).square = n₁.square * n₂.square := by
  unfold Nat.square
  rw [← Nat.mul_assoc]
  have h: n₁ * n₂ * n₁ = n₁ * n₁ * n₂ := by rw [Nat.mul_comm, Nat.mul_assoc]
  rw [h, Nat.mul_assoc]

def fooBar (x: Nat) := 5

theorem sillyFact1 (n: Nat): fooBar n + 1 = fooBar (n + 1) + 1 := by
  simp
  rfl

def barFoo: Nat → Nat
  | .zero => 5
  | .succ _ => 5

theorem sillyFact2 (n: Nat): barFoo n + 1 = barFoo (n + 1) + 1 := by
  cases n with
    | zero => rfl
    | succ n =>
      simp
      rfl

theorem sillyFact2Again (n: Nat): barFoo n + 1 = barFoo (n + 1) + 1 := by
  unfold barFoo
  cases n <;> rfl

/-
## Using `cases` on Compound Expressions
-/

def Nat.sillyFun (n: Nat): Bool :=
  if n == 3
  then false
  else if n == 5
       then false
       else false

theorem Nat.sillyFunFalse (n: Nat): n.sillyFun = false := by
  unfold Nat.sillyFun
  cases (n == 3) with
    | false => simp
    | true =>
      cases (n == 5) with
        | false => simp
        | true => simp

theorem PolyList.splitZip (l: PolyList (PolyProd α β)) (l₁: PolyList α) (l₂: PolyList β) (h: l.split = ⟨l₁, l₂⟩): l₁.zip l₂ = l := by
  sorry
