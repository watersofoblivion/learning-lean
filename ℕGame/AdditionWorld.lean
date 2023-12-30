/-
# Addition World
-/

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»

/--
## Zero Add.  Explicitly uses `0`, not `ℕ.zero`
-/

theorem ℕ.add0L: ∀ n: ℕ, 0 + n = n
  | .zero => rfl
  | .succ n =>
    calc 0 + n.succ
      _ = (0 + n).succ := ℕ.addSucc 0 n
      _ = n.succ       := congrArg ℕ.succ (ℕ.add0L n)

example (n: ℕ): 0 + n = n := by
  induction n with
    | zero => rfl
    | succ n ihₙ => rw [ℕ.addSucc, ihₙ]

/--
## Zero Add.  Explicitly uses `ℕ.zero`, not `0`.
-/

theorem ℕ.zeroAdd: ∀ n: ℕ, .zero + n = n
  | .zero => rfl
  | .succ n =>
    calc ℕ.zero + n.succ
      _ = (ℕ.zero + n).succ := ℕ.addSucc ℕ.zero n
      _ = n.succ            := congrArg ℕ.succ (ℕ.zeroAdd n)

example (n: ℕ): .zero + n = n := by
  induction n with
    | zero => rfl
    | succ n ihₙ => rw [ℕ.addSucc, ihₙ]

/--
## Successor Add
-/

theorem ℕ.succAdd: ∀ n₁ n₂: ℕ, n₁.succ + n₂ = (n₁ + n₂).succ
  | n₁, .zero =>
    calc n₁.succ + .zero
      _ = n₁.succ := ℕ.addZero n₁.succ
      _ = (n₁ + .zero).succ := congrArg ℕ.succ (Eq.symm (ℕ.addZero n₁))
  | n₁, .succ n₂ =>
    calc n₁.succ + n₂.succ
      _ = (n₁.succ + n₂).succ := ℕ.addSucc n₁.succ n₂
      _ = (n₁ + n₂).succ.succ := congrArg ℕ.succ (ℕ.succAdd n₁ n₂)
      _ = (n₁ + n₂.succ).succ := congrArg ℕ.succ (Eq.symm (ℕ.addSucc n₁ n₂))

example (n₁ n₂: ℕ): n₁.succ + n₂ = (n₁ + n₂).succ := by
  induction n₂ with
    | zero => repeat rw [ℕ.addZero]
    | succ n₂ ihn₂ =>
      repeat rw [ℕ.addSucc]
      rw [ihn₂]

/--
## Add Commutivity
-/

theorem ℕ.addComm: ∀ n₁ n₂: ℕ, n₁ + n₂ = n₂ + n₁
  | n₁, .zero =>
    calc n₁ + .zero
      _ = n₁         := ℕ.addZero n₁
      _ = .zero + n₁ := Eq.symm (ℕ.zeroAdd n₁)
  | n₁, .succ n₂ =>
    calc n₁ + n₂.succ
      _ = (n₁ + n₂).succ := ℕ.addSucc n₁ n₂
      _ = (n₂ + n₁).succ := congrArg ℕ.succ (ℕ.addComm n₁ n₂)
      _ = n₂.succ + n₁   := Eq.symm (ℕ.succAdd n₂ n₁)

example (n₁ n₂: ℕ): n₁ + n₂ = n₂ + n₁ := by
  induction n₁ with
    | zero => rw [ℕ.addZero, ℕ.zeroAdd]
    | succ n₁ ihn₁ => rw [ℕ.addSucc, ℕ.succAdd, ihn₁]

/--
## Add Associativity
-/

theorem ℕ.addAssoc: ∀ n₁ n₂ n₃: ℕ, (n₁ + n₂) + n₃ = n₁ + (n₂ + n₃)
  | .zero, n₂, n₃ =>
    calc (ℕ.zero + n₂) + n₃
      _ = n₂ + n₃            := congrFun (congrArg ℕ.add (ℕ.zeroAdd n₂)) n₃
      _ = ℕ.zero + (n₂ + n₃) := Eq.symm (ℕ.zeroAdd (n₂ + n₃))
  | .succ n₁, n₂, n₃ =>
    calc (n₁.succ + n₂) + n₃
      _ = (n₁ + n₂).succ + n₃   := congrFun (congrArg ℕ.add (ℕ.succAdd n₁ n₂)) n₃
      _ = ((n₁ + n₂) + n₃).succ := ℕ.succAdd (n₁ + n₂) n₃
      _ = (n₁ + (n₂ + n₃)).succ := congrArg ℕ.succ (ℕ.addAssoc n₁ n₂ n₃)
      _ = n₁.succ + (n₂ + n₃)   := Eq.symm (ℕ.succAdd n₁ (n₂ + n₃))

example (n₁ n₂ n₃: ℕ): (n₁ + n₂) + n₃ = n₁ + (n₂ + n₃) := by
  induction n₁ with
    | zero => rw [ℕ.zeroAdd, ℕ.zeroAdd]
    | succ n₁ ihn₁ =>
      repeat rw [ℕ.succAdd]
      rw [ihn₁]

/--
## Add Right Commutivity
-/

theorem ℕ.addRightComm (n₁ n₂ n₃: ℕ): n₁ + n₂ + n₃ = n₁ + n₃ + n₂ :=
  calc n₁ + n₂ + n₃
    _ = n₁ + (n₂ + n₃) := ℕ.addAssoc n₁ n₂ n₃
    _ = n₁ + (n₃ + n₂) := congrArg (ℕ.add n₁) (ℕ.addComm n₂ n₃)
    _ = n₁ + n₃ + n₂   := Eq.symm (ℕ.addAssoc n₁ n₃ n₂)

example (n₁ n₂ n₃: ℕ): n₁ + n₂ + n₃ = n₁ + n₃ + n₂ := by
  rw [ℕ.addAssoc, ℕ.addComm n₂ n₃, ← ℕ.addAssoc]
