/-
# Addition World
-/

import «ℕGame».«ℕ»
import «ℕGame».«TutorialWorld»

namespace Term
  /-
  ## Zero Add.  Explicitly uses `0`, not `ℕ.zero`
  -/

  theorem add0L: ∀ n: ℕ, 0 + n = n
    | .zero => rfl
    | .succ n =>
      show 0 + n.succ = n.succ from
        calc 0 + n.succ
          _ = (0 + n).succ := ℕ.addSucc 0 n
          _ = n.succ       := congrArg ℕ.succ (add0L n)

  /-
  ## Zero Add.  Explicitly uses `ℕ.zero`, not `0`.
  -/

  theorem zeroAdd: ∀ n: ℕ, .zero + n = n
    | .zero => rfl
    | .succ n =>
      calc ℕ.zero + n.succ
        _ = (ℕ.zero + n).succ := ℕ.addSucc ℕ.zero n
        _ = n.succ            := congrArg ℕ.succ (zeroAdd n)

  /-
  ## Successor Add
  -/

  theorem succAdd: ∀ n₁ n₂: ℕ, n₁.succ + n₂ = (n₁ + n₂).succ
    | n₁, .zero =>
      calc n₁.succ + .zero
        _ = n₁.succ := ℕ.addZero n₁.succ
        _ = (n₁ + .zero).succ := congrArg ℕ.succ (Eq.symm (ℕ.addZero n₁))
    | n₁, .succ n₂ =>
      calc n₁.succ + n₂.succ
        _ = (n₁.succ + n₂).succ := ℕ.addSucc n₁.succ n₂
        _ = (n₁ + n₂).succ.succ := congrArg ℕ.succ (succAdd n₁ n₂)
        _ = (n₁ + n₂.succ).succ := congrArg ℕ.succ (Eq.symm (ℕ.addSucc n₁ n₂))

  /-
  ## Add Commutivity
  -/

  theorem addComm: ∀ n₁ n₂: ℕ, n₁ + n₂ = n₂ + n₁
    | n₁, .zero =>
      calc n₁ + .zero
        _ = n₁         := ℕ.addZero n₁
        _ = .zero + n₁ := Eq.symm (zeroAdd n₁)
    | n₁, .succ n₂ =>
      calc n₁ + n₂.succ
        _ = (n₁ + n₂).succ := ℕ.addSucc n₁ n₂
        _ = (n₂ + n₁).succ := congrArg ℕ.succ (addComm n₁ n₂)
        _ = n₂.succ + n₁   := Eq.symm (succAdd n₂ n₁)

  /-
  ## Add Associativity
  -/

  theorem addAssoc: ∀ n₁ n₂ n₃: ℕ, (n₁ + n₂) + n₃ = n₁ + (n₂ + n₃)
    | .zero, n₂, n₃ =>
      calc (ℕ.zero + n₂) + n₃
        _ = n₂ + n₃            := congrFun (congrArg ℕ.add (zeroAdd n₂)) n₃
        _ = ℕ.zero + (n₂ + n₃) := Eq.symm (zeroAdd (n₂ + n₃))
    | .succ n₁, n₂, n₃ =>
      calc (n₁.succ + n₂) + n₃
        _ = (n₁ + n₂).succ + n₃   := congrFun (congrArg ℕ.add (succAdd n₁ n₂)) n₃
        _ = ((n₁ + n₂) + n₃).succ := succAdd (n₁ + n₂) n₃
        _ = (n₁ + (n₂ + n₃)).succ := congrArg ℕ.succ (addAssoc n₁ n₂ n₃)
        _ = n₁.succ + (n₂ + n₃)   := Eq.symm (succAdd n₁ (n₂ + n₃))

  /-
  ## Add Right Commutivity
  -/

  theorem addRightComm (n₁ n₂ n₃: ℕ): n₁ + n₂ + n₃ = n₁ + n₃ + n₂ :=
    calc n₁ + n₂ + n₃
      _ = n₁ + (n₂ + n₃) := addAssoc n₁ n₂ n₃
      _ = n₁ + (n₃ + n₂) := congrArg (ℕ.add n₁) (addComm n₂ n₃)
      _ = n₁ + n₃ + n₂   := Eq.symm (addAssoc n₁ n₃ n₂)
end Term

namespace Tactic
  /-
  ## Zero Add.  Explicitly uses `0`, not `ℕ.zero`
  -/

  @[local simp]
  theorem add0L (n: ℕ): 0 + n = n := by
    induction n with
      | zero => rfl
      | succ n ihₙ => simp [ihₙ]

  /-
  ## Zero Add.  Explicitly uses `ℕ.zero`, not `0`.
  -/

  @[local simp]
  theorem zeroAdd (n: ℕ): .zero + n = n := by
    induction n with
      | zero => rfl
      | succ n ihₙ => simp [ihₙ]

  /-
  ## Successor Add
  -/

  @[local simp]
  theorem succAdd (n₁ n₂: ℕ): n₁.succ + n₂ = (n₁ + n₂).succ := by
    induction n₂ with
      | zero => simp
      | succ n₂ ihn₂ => simp [ihn₂]

  /-
  ## Add Commutivity
  -/

  @[local simp]
  theorem addComm (n₁ n₂: ℕ): n₁ + n₂ = n₂ + n₁ := by
    induction n₁ with
      | zero => simp
      | succ n₁ ihn₁ => simp [ihn₁]

  /-
  ## Add Associativity
  -/

  @[local simp]
  theorem addAssoc (n₁ n₂ n₃: ℕ): (n₁ + n₂) + n₃ = n₁ + (n₂ + n₃) := by
    induction n₁ with
      | zero => simp
      | succ n₁ ihn₁ =>
        repeat rw [succAdd]
        rw [ihn₁]

  /-
  ## Add Right Commutivity
  -/

  @[local simp]
  theorem addRightComm (n₁ n₂ n₃: ℕ): n₁ + n₂ + n₃ = n₁ + n₃ + n₂ := by
    rw [addAssoc, addComm n₂ n₃, ← addAssoc]
end Tactic

namespace Blended
  /-
  ## Zero Add.  Explicitly uses `0`, not `ℕ.zero`
  -/

  @[local simp]
  theorem add0L: ∀ n: ℕ, 0 + n = n
    | .zero => rfl
    | .succ n =>
      calc 0 + n.succ
        _ = (0 + n).succ := by simp
        _ = n.succ       := by rw [add0L n]

  /-
  ## Zero Add.  Explicitly uses `ℕ.zero`, not `0`.
  -/

  @[local simp]
  theorem zeroAdd: ∀ n: ℕ, .zero + n = n
    | .zero => rfl
    | .succ n =>
      calc ℕ.zero + n.succ
        _ = (ℕ.zero + n).succ := by simp
        _ = n.succ            := by rw [zeroAdd n]

  /-
  ## Successor Add
  -/

  @[local simp]
  theorem succAdd: ∀ n₁ n₂: ℕ, n₁.succ + n₂ = (n₁ + n₂).succ
    | n₁, .zero => by repeat rw [ℕ.addZero]
    | n₁, .succ n₂ =>
      calc n₁.succ + n₂.succ
        _ = (n₁.succ + n₂).succ := by simp
        _ = (n₁ + n₂).succ.succ := by rw [succAdd n₁ n₂]
        _ = (n₁ + n₂.succ).succ := by simp

  /-
  ## Add Commutivity
  -/

  @[local simp]
  theorem addComm: ∀ n₁ n₂: ℕ, n₁ + n₂ = n₂ + n₁
    | n₁, .zero => by simp
    | n₁, .succ n₂ => by
      calc n₁ + n₂.succ
        _ = (n₁ + n₂).succ := by simp
        _ = (n₂ + n₁).succ := by rw [addComm n₁ n₂]
        _ = n₂.succ + n₁   := by simp

  /-
  ## Add Associativity
  -/

  @[local simp]
  theorem addAssoc: ∀ n₁ n₂ n₃: ℕ, (n₁ + n₂) + n₃ = n₁ + (n₂ + n₃)
    | .zero, n₂, n₃ => by simp
    | .succ n₁, n₂, n₃ =>
      calc (n₁.succ + n₂) + n₃
        _ = ((n₁ + n₂) + n₃).succ := by simp
        _ = (n₁ + (n₂ + n₃)).succ := by rw [addAssoc n₁ n₂ n₃]
        _ = n₁.succ + (n₂ + n₃)   := by simp

  /-
  ## Add Right Commutivity
  -/

  @[local simp]
  theorem addRightComm (n₁ n₂ n₃: ℕ): n₁ + n₂ + n₃ = n₁ + n₃ + n₂ :=
    calc n₁ + n₂ + n₃
      _ = n₁ + (n₂ + n₃) := by rw [addAssoc]
      _ = n₁ + (n₃ + n₂) := by rw [addComm n₂ n₃]
      _ = n₁ + n₃ + n₂   := by rw [addAssoc]
end Blended
