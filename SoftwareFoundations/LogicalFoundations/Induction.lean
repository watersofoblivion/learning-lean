import «SoftwareFoundations».«LogicalFoundations».Basics

/-
# Induction
-/

/-
## Proof By Induction
-/

/- ### Add Zero Right -/

theorem addZeroRight: ∀ n: Nat, n + 0 = n
  | .zero => rfl
  | .succ n => congrArg Nat.succ (addZeroRight n)

example (n: Nat): n + 0 = n :=
  have base: 0 + 0 = 0 := Nat.add_zero 0
  have ind (k: Nat) (h: k + 0 = k): k.succ + 0 = k.succ :=
    calc k.succ + 0
      _ = (k + 0).succ := Nat.succ_add k 0
      _ = k.succ       := congrArg Nat.succ h
  Nat.recOn n base ind

example (n: Nat): n + 0 = n := by
  induction n with
    | zero => rfl
    | succ _ ih => rw [Nat.succ_add, ih]

/- ### Minus Self -/

theorem minusSelf: ∀ n: Nat, n - n = 0
  | .zero => rfl
  | .succ n =>
    calc n.succ - n.succ
      _ = n - n := Nat.succ_sub_succ n n
      _ = 0     := minusSelf n

example (n: Nat): n - n = 0 :=
  have base: 0 - 0 = 0 := Nat.sub_zero 0
  have ind (k: Nat) (h: k - k = 0): k.succ - k.succ = 0 :=
    calc k.succ - k.succ
      _ = k - k := Nat.succ_sub_succ k k
      _ = 0     := h
  Nat.recOn n base ind

example (n: Nat): n - n = 0 := by
  induction n with
    | zero => rfl
    | succ _ ih => rw [Nat.succ_sub_succ, ih]

/-
#### Exercises
-/

/- ##### Mul Zero Right -/

theorem mulZeroRight: ∀ n: Nat, n * 0 = 0
  | .zero => rfl
  | .succ n =>
    calc n.succ * 0
      _ = n * 0 + 0 := Nat.succ_mul n 0
      _ = n * 0     := Nat.add_zero (n * 0)
      _ = 0         := mulZeroRight n

example (n: Nat): n * 0 = 0 :=
  have base: 0 * 0 = 0 := Nat.zero_mul 0
  have ind (k: Nat) (h: k * 0 = 0): k.succ * 0 = 0 :=
    calc k.succ * 0
      _ = k * 0 + 0 := Nat.succ_mul k 0
      _ = k * 0     := Nat.add_zero (k * 0)
      _ = 0         := h
  Nat.recOn n base ind

example (n: Nat): n * 0 = 0 := by
  induction n with
    | zero => rfl
    | succ n ih => rw [Nat.succ_mul, Nat.add_zero, ih]

/- ##### Plus N Succ -/

example: ∀ n₁ n₂: Nat, Nat.succ (n₁ + n₂) = n₁ + (Nat.succ n₂)
  | _, _ => rfl

example (n₁ n₂: Nat): Nat.succ (n₁ + n₂) = n₁ + (Nat.succ n₂) :=
  have base: (0 + n₂).succ = 0 + n₂.succ := rfl
  have ind (k: Nat) (h: (k + n₂).succ = k + n₂.succ): (k.succ + n₂).succ = k.succ + n₂.succ :=
    calc (k.succ + n₂).succ
      _ = (k + n₂).succ.succ := Nat.succ_add k n₂.succ
      _ = (k + n₂.succ).succ := congrArg Nat.succ h
      _ = k.succ + n₂.succ   := Eq.symm (Nat.succ_add k n₂.succ)
  Nat.recOn n₁ base ind

example (n₁ n₂: Nat): Nat.succ (n₁ + n₂) = n₁ + (Nat.succ n₂) :=
  have base: (n₁ + 0) + 1= n₁ + 1 :=
    calc (n₁ + 0) + 1
      _ = (n₁ + 1) + 0 := Eq.symm (Nat.succ_add n₁ 0)
      _ = n₁ + (1 + 0) := Nat.add_assoc n₁ 1 0
      _ = n₁ + 1       := rfl
  have ind (k: Nat) (h: (n₁ + k).succ = n₁ + k.succ): (n₁ + k.succ).succ = n₁ + k.succ.succ :=
    calc (n₁ + (k + 1)) + 1
      _ = (n₁ + k).succ.succ := Nat.add_succ n₁ k.succ
      _ = (n₁ + k.succ).succ := congrArg Nat.succ h
  Nat.recOn n₂ base ind

example (n₁ n₂: Nat): Nat.succ (n₁ + n₂) = n₁ + (Nat.succ n₂) := by
  induction n₁ with
    | zero => rfl
    | succ _ ih => rw [Nat.succ_add, ih, Nat.succ_add]

example (n₁ n₂: Nat): Nat.succ (n₁ + n₂) = n₁ + (Nat.succ n₂) := by
  induction n₂ with
    | zero => rfl
    | succ _ ih => rw [Nat.add_succ, ih, ←Nat.add_succ]

/- ##### Add Comm -/

theorem addComm: ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁
  | .zero, .zero => rfl
  | .zero, .succ n₂ =>
    calc 0 + n₂.succ
      _ = (0 + n₂).succ := Nat.add_succ 0 n₂
      _ = n₂.succ       := Nat.zero_add n₂.succ
      _ = n₂.succ + 0   := Eq.symm (Nat.add_zero n₂.succ)
  | .succ n₁, .zero =>
    calc n₁.succ + 0
      _ = (n₁ + 0).succ := Nat.succ_add n₁ 0
      _ = n₁.succ       := Nat.add_zero n₁.succ
      _ = 0 + n₁.succ   := Eq.symm (Nat.zero_add n₁.succ)
  | .succ n₁, .succ n₂ =>
    calc n₁.succ + n₂.succ
      _ = (n₁.succ + n₂).succ := Nat.add_succ n₁.succ n₂
      _ = (n₁ + n₂).succ.succ := Nat.succ_add n₁ n₂.succ
      _ = (n₂ + n₁).succ.succ := congrArg (Nat.succ ∘ Nat.succ) (addComm n₁ n₂)
      _ = (n₂ + n₁.succ).succ := Eq.symm (Nat.add_succ n₂ n₁.succ)
      _ = n₂.succ + n₁.succ   := Eq.symm (Nat.succ_add n₂ n₁.succ)

example (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ :=
  have base: 0 + n₂ = n₂ + 0 :=
    calc 0 + n₂
      _ = n₂     := Nat.zero_add n₂
      _ = n₂ + 0 := Eq.symm (Nat.add_zero n₂)
  have ind (k: Nat) (h: k + n₂ = n₂ + k): k.succ + n₂ = n₂ + k.succ :=
    calc k.succ + n₂
      _ = (k + n₂).succ := Nat.succ_add k n₂
      _ = (n₂ + k).succ := congrArg Nat.succ h
      _ = n₂ + k.succ   := Eq.symm (Nat.add_succ n₂ k)
  Nat.recOn n₁ base ind

example (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ :=
  have base: n₁ + 0 = 0 + n₁ :=
    calc n₁ + 0
      _ = n₁     := Nat.add_zero n₁
      _ = 0 + n₁ := Eq.symm (Nat.zero_add n₁)
  have ind (k: Nat) (h: n₁ + k = k + n₁): n₁ + k.succ = k.succ + n₁ :=
    calc n₁ + k.succ
      _ = (n₁ + k).succ := Nat.add_succ n₁ k
      _ = (k + n₁).succ := congrArg Nat.succ h
      _ = k.succ + n₁   := Eq.symm (Nat.succ_add k n₁)
  Nat.recOn n₂ base ind

example (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ := by
  induction n₁ with
    | zero => simp
    | succ _ ih => rw [Nat.succ_add, Nat.add_succ, ih]

example (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ := by
  induction n₂ with
    | zero => simp
    | succ _ ih => rw [Nat.succ_add, Nat.add_succ, ih]

/- ##### Add Assoc -/

theorem addAssoc: ∀ n₁ n₂ n₃: Nat, n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃
  | .zero, .zero, .zero => rfl
  | .zero, .zero, .succ n₃ =>
    calc 0 + (0 + n₃.succ)
      _ = 0 + n₃.succ       := Nat.zero_add (0 + n₃.succ)
      _ = n₃.succ + 0       := Nat.add_comm 0 n₃.succ
      _ = n₃.succ + (0 + 0) := congrArg (Nat.add n₃.succ) (Eq.symm (Nat.add_zero 0))
      _ = (0 + 0) + n₃.succ := Nat.add_comm n₃.succ (0 + 0)
  | .zero, .succ n₂, .zero =>
    calc 0 + (n₂.succ + 0)
      _ = n₂.succ + 0       := Nat.zero_add (n₂.succ + 0)
      _ = 0 + n₂.succ       := Nat.add_comm n₂.succ 0
      _ = 0 + (0 + n₂.succ) := congrArg (Nat.add 0) (Eq.symm (Nat.zero_add n₂.succ))
      _ = (0 + n₂.succ) + 0 := Nat.add_comm 0 (0 + n₂.succ)
  | .zero, .succ n₂, .succ n₃ =>
    calc 0 + (n₂.succ + n₃.succ)
      _ = n₂.succ + n₃.succ       := Nat.zero_add (n₂.succ + n₃.succ)
      _ = n₃.succ + n₂.succ       := Nat.add_comm n₂.succ n₃.succ
      _ = n₃.succ + (0 + n₂.succ) := congrArg (Nat.add n₃.succ) (Eq.symm (Nat.zero_add n₂.succ))
      _ = (0 + n₂.succ) + n₃.succ := Nat.add_comm n₃.succ (0 + n₂.succ)
  | .succ n₁, .zero, .zero =>
    calc n₁.succ + (0 + 0)
      _ = n₁.succ           := rfl
      _ = n₁.succ + 0       := Eq.symm (Nat.add_zero n₁.succ)
      _ = (n₁.succ + 0) + 0 := Eq.symm (Nat.add_zero (n₁.succ + 0))
  | .succ n₁, .zero, .succ n₃ =>
    calc n₁.succ + (0 + n₃.succ)
      _ = n₁.succ + n₃.succ       := congrArg (Nat.add n₁.succ) (Nat.zero_add n₃.succ)
      _ = n₃.succ + n₁.succ       := Nat.add_comm n₁.succ n₃.succ
      _ = n₃.succ + (n₁.succ + 0) := congrArg (Nat.add n₃.succ) (Eq.symm (Nat.add_zero n₁.succ))
      _ = (n₁.succ + 0) + n₃.succ := Nat.add_comm n₃.succ (n₁.succ + 0)
  | .succ n₁, .succ n₂, .zero =>
    calc n₁.succ + (n₂.succ + 0)
      _ = n₁.succ + n₂.succ       := rfl
      _ = (n₁.succ + n₂.succ) + 0 := Eq.symm (Nat.add_zero (n₁.succ + n₂.succ))
  | .succ n₁, .succ n₂, .succ n₃ =>
    calc n₁.succ + (n₂.succ + n₃.succ)
      _ = n₁.succ + (n₂.succ + n₃).succ := congrArg (Nat.add n₁.succ) (Nat.add_succ n₂.succ n₃)
      _ = n₁.succ + (n₂ + n₃).succ.succ := congrArg (Nat.add n₁.succ) (Nat.succ_add n₂ n₃.succ)
      _ = (n₂ + n₃).succ.succ + n₁.succ := Nat.add_comm n₁.succ (n₂ + n₃).succ.succ
      _ = ((n₂ + n₃) + n₁).succ.succ.succ := sorry -- Nat.add_succ (n₂ + n₃).succ.succ n₁
      _ = (n₁ + (n₂ + n₃)).succ.succ.succ := congrArg (Nat.succ ∘ Nat.succ ∘ Nat.succ) (Nat.add_comm (n₂ + n₃) n₁)
      _ = ((n₁ + n₂) + n₃).succ.succ.succ := congrArg (Nat.succ ∘ Nat.succ ∘ Nat.succ) (addAssoc n₁ n₂ n₃)
      _ = (n₁ + n₂).succ.succ + n₃.succ := sorry
      _ = n₃.succ + (n₁ + n₂).succ.succ := Nat.add_comm (n₁ + n₂).succ.succ n₃.succ
      _ = n₃.succ + (n₁ + n₂.succ).succ := congrArg (Nat.add n₃.succ) (Eq.symm (Nat.add_succ n₁ n₂.succ))
      _ = n₃.succ + (n₁.succ + n₂.succ) := congrArg (Nat.add n₃.succ) (Eq.symm (Nat.succ_add n₁ n₂.succ))
      _ = (n₁.succ + n₂.succ) + n₃.succ := Nat.add_comm n₃.succ (n₁.succ + n₂.succ)

example (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃ :=
  have base: 0 + (n₂ + n₃) = (0 + n₂) + n₃ :=
    calc 0 + (n₂ + n₃)
      _ = n₂ + n₃ := Nat.zero_add (n₂ + n₃)
      _ = n₃ + n₂ := Nat.add_comm n₂ n₃
      _ = n₃ + (0 + n₂) := congrArg (Nat.add n₃) (Eq.symm (Nat.zero_add n₂))
      _ = (0 + n₂) + n₃ := Nat.add_comm n₃ (0 + n₂)
  have ind (k: Nat) (h: k + (n₂ + n₃) = (k + n₂) + n₃): k.succ + (n₂ + n₃) = (k.succ + n₂) + n₃ :=
    calc k.succ + (n₂ + n₃)
      _ = (k + (n₂ + n₃)).succ := Nat.succ_add k (n₂ + n₃)
      _ = ((k + n₂) + n₃).succ := congrArg Nat.succ h
      _ = (k + n₂).succ + n₃ := Eq.symm (Nat.succ_add (k + n₂) n₃)
      _ = n₃ + (k + n₂.succ) := Nat.add_comm (k + n₂.succ) n₃
      _ = n₃ + (k.succ + n₂) := congrArg (Nat.add n₃) (Eq.symm (Nat.succ_add k n₂))
      _ = (k.succ + n₂) + n₃ := Nat.add_comm n₃ (k.succ + n₂)
  Nat.recOn n₁ base ind

example (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃ := by
  induction n₁ with
    | zero => simp
    | succ n ih => rw [Nat.succ_add, ih, ← Nat.succ_add, ← Nat.succ_add]

example (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃ := by
  induction n₂ with
    | zero => simp
    | succ n ih => rw [Nat.succ_add n n₃, Nat.add_succ, ih, ← Nat.succ_add, ← Nat.add_succ]

example (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃ := by
  induction n₃ with
    | zero => simp
    | succ n ih => rw [Nat.add_succ, Nat.add_succ, ih, ← Nat.add_succ]

/- ##### Double Plus -/

def Nat.double: Nat → Nat
  | .zero => .zero
  | .succ n => (double n).succ.succ

/- TODO: Get rid of tactic block -/
theorem Nat.doublePlus: ∀ n: Nat, n.double = n + n
  | .zero => rfl
  | .succ n =>
    calc n.succ.double
      _ = n.double.succ.succ := by rw [Nat.double]
      _ = (n + n).succ.succ  := congrArg (Nat.succ ∘ Nat.succ) (Nat.doublePlus n)
      _ = (n.succ + n).succ  := Eq.symm (Nat.succ_add n n.succ)
      _ = n.succ + n.succ    := Eq.symm (Nat.add_succ n.succ n)

example (n: Nat): n.double = n + n := by
  induction n with
    | zero => rfl
    | succ n ihn =>
      simp [Nat.double, Nat.add_succ]
      rw [ihn]
      rw [Nat.succ_add]

/- #### Eq Reflexive -/

/- TODO: Get rid of tactic block -/
theorem 𝔹.eqRefl: ∀ n: Nat, n.eq n
  | .zero => rfl
  | .succ n =>
    calc n.succ.eq n.succ
      _ = n.eq n := by rw [Nat.eq]
      _ = .true  := 𝔹.eqRefl n

example (n: Nat): n.eq n := by
  induction n with
    | zero => rfl
    | succ n ihₙ => rw [Nat.eq, ihₙ]

/- ##### Even Succ -/

theorem Nat.evenSucc: ∀ n: Nat, n.succ.isEven = ¬n.isEven
  | .zero => sorry
  | .succ n => sorry

example (n: Nat): n.succ.isEven = ¬n.isEven := by
  induction n with
    | zero => simp
    | succ n ihₙ =>
      cases n with
        | zero => simp
        | succ n =>
          rw [ihₙ]
          simp [Nat.isEven]

/-
## Proofs Within Proofs
-/

/- ### Mult Zero Plus -/

example (n₁ n₂: Nat): (n₁ + 0 + 0) * n₂ = n₁ * n₂ :=
  have h: n₁ + 0 + 0 = n₁ := rfl
  calc (n₁ + 0 + 0) * n₂
    _ = n₂ * (n₁ + 0 + 0) := Nat.mul_comm (n₁ + 0 + 0) n₂
    _ = n₂ * n₁ := congrArg (Nat.mul n₂) h
    _ = n₁ * n₂ := Nat.mul_comm n₂ n₁

example (n₁ n₂: Nat): (n₁ + 0 + 0) * n₂ = n₁ * n₂ := by
  have h: n₁ + 0 + 0 = n₁ := by simp
  rw [h]

/- ### Plus Re-arrange -/

example (n₁ n₂ n₃ n₄: Nat): (n₁ + n₂) + (n₃ + n₄) = (n₂ + n₁) + (n₃ + n₄) :=
  have h: n₁ + n₂ = n₂ + n₁ := Nat.add_comm n₁ n₂
  calc (n₁ + n₂) + (n₃ + n₄)
    _ = (n₃ + n₄) + (n₁ + n₂) := Nat.add_comm (n₁ + n₂) (n₃ + n₄)
    _ = (n₃ + n₄) + (n₂ + n₁) := congrArg (Nat.add (n₃ + n₄)) h
    _ = (n₂ + n₁) + (n₃ + n₄) := Nat.add_comm (n₃ + n₄) (n₂ + n₁)

example (n₁ n₂ n₃ n₄: Nat): (n₁ + n₂) + (n₃ + n₄) = (n₂ + n₁) + (n₃ + n₄) := by
  have h: n₁ + n₂ = n₂ + n₁ := by rw [Nat.add_comm]
  rw [h]

/-
## Formal vs. Informal Proofs
-/

/-
#### Exercises
-/

/- ##### Add Shuffle 3 -/

example (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) :=
  calc n₁ + (n₂ + n₃)
    _ = n₁ + (n₃ + n₂) := congrArg (Nat.add n₁) (Nat.add_comm n₂ n₃)
    _ = (n₁ + n₃) + n₂ := Eq.symm (Nat.add_assoc n₁ n₃ n₂)
    _ = n₂ + (n₁ + n₃) := Nat.add_comm (n₁ + n₃) n₂

example (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) := by
  rw [← Nat.add_assoc, Nat.add_comm n₁ n₂, Nat.add_assoc]

/- ##### Mul Comm -/

theorem Nat.mulComm₁: ∀ n₁ n₂: Nat, n₁ * n₂ = n₂ * n₁
  | .zero, n₂ => Nat.zero_mul n₂
  | .succ n₁, n₂ =>
    calc n₁.succ * n₂
      _ = n₁ * n₂ + n₂ := Nat.succ_mul n₁ n₂
      _ = n₂ + n₁ * n₂ := Nat.add_comm (n₁ * n₂) n₂
      _ = n₂ + n₂ * n₁ := congrArg (Nat.add n₂) (Nat.mulComm₁ n₁ n₂)
      _ = n₂ * n₁ + n₂ := Nat.add_comm n₂ (n₂ * n₁)
      _ = n₂ * n₁.succ := Eq.symm (Nat.mul_succ n₂ n₁)

theorem Nat.mulComm₂: ∀ n₁ n₂: Nat, n₁ * n₂ = n₂ * n₁
  | n₁, .zero => Eq.symm (Nat.zero_mul n₁)
  | n₁, .succ n₂ =>
    calc n₁ * n₂.succ
      _ = n₁ * n₂ + n₁ := Nat.mul_succ n₁ n₂
      _ = n₁ + n₁ * n₂ := Nat.add_comm (n₁ * n₂) n₁
      _ = n₁ + n₂ * n₁ := congrArg (Nat.add n₁) (Nat.mulComm₂ n₁ n₂)
      _ = n₂ * n₁ + n₁ := Nat.add_comm n₁ (n₂ * n₁)
      _ = n₂.succ * n₁ := Eq.symm (Nat.succ_mul n₂ n₁)

example (n₁ n₂: Nat): n₁ * n₂ = n₂ * n₁ := by
  induction n₁ with
    | zero => simp
    | succ n₁ ihn₁ => rw [Nat.succ_mul, ihn₁, Nat.mul_succ]

example (n₁ n₂: Nat): n₁ * n₂ = n₂ * n₁ := by
  induction n₂ with
    | zero => simp
    | succ n₂ ihn₂ => rw [Nat.mul_succ, ihn₂, Nat.succ_mul]

/- ##### Leq Compat Left -/

/- TODO: Get rid of tactic block -/
theorem Nat.leqCompatL (n₁ n₂ n₃: Nat) (h: n₁.less_eq n₂): (n₃ + n₁).less_eq (n₃ + n₂) :=
  match n₃ with
    | .zero =>
      calc (0 + n₁).less_eq (0 + n₂)
        _ = n₁.less_eq n₂ := by simp [Nat.zero_add]
        _ = .true         := h
    | .succ n₃ =>
      calc (n₃.succ + n₁).less_eq (n₃.succ + n₂)
        _ = (n₃ + n₁).succ.less_eq (n₃ + n₂).succ := by rw [Nat.succ_add, Nat.succ_add]
        _ = (n₃ + n₁).less_eq (n₃ + n₂)           := by rw [Nat.less_eq]
        _ = .true                                 := Nat.leqCompatL n₁ n₂ n₃ h

example (n₁ n₂ n₃: Nat) (h: n₁.less_eq n₂): (n₃ + n₁).less_eq (n₃ + n₂) := by
  induction n₃ with
    | zero =>
      rw [Nat.zero_add, Nat.zero_add]
      exact h
    | succ n₃ ihn₃ =>
      rw [Nat.succ_add, Nat.succ_add]
      rw [Nat.less_eq]
      exact ihn₃

theorem Nat.lessEqRefl (n₁ n₂: Nat) (h: n₁.less_eq n₂): n₂.less_eq n₂ := sorry
example (n₁ n₂: Nat) (h: n₁.less_eq n₂): n₂.less_eq n₂ := by sorry

theorem Nat.zeroNeSucc: ∀ n: Nat, n ≠ n.succ
  | .zero => sorry
  | .succ n => sorry

example (n: Nat): n ≠ n.succ := by
  induction n with
    | zero =>
      unfold Ne Not
      intro h
      contradiction
    | succ n ihₙ =>
      unfold Ne Not
      unfold Ne Not at ihₙ
      intro h
      rw [Nat.succ_eq_add_one] at ihₙ
      apply ihₙ
      rw [Nat.succ.injEq] at h
      assumption

theorem 𝔹.andFalseR (b: 𝔹): b.and .false = false := by
  cases b <;> rfl

theorem Nat.succNeZero (n: Nat): ¬n.succ = 0 := by
  cases n <;> simp

theorem Nat.multOneLeft (n: Nat): 1 * n = n := by
  simp

theorem Nat.all3Spec (b₁ b₂: 𝔹): (b₁.neg.or b₂.neg).or (b₁.and b₂) = .true := by
  cases b₁ <;> cases b₂ <;> rfl

theorem Nat.mulAddDistRight (n₁ n₂ n₃: Nat): (n₁ + n₂) * n₃ = (n₁ * n₃) + (n₂ * n₃) := by
  sorry

theorem Nat.mulAssoc (n₁ n₂ n₃: Nat): n₁ * (n₂ * n₃) = n₁ * n₂ * n₃ := by
  sorry

/-
## Nat to Bin and Back to Nat
-/

theorem Bin.toNatPreservesIncr (b: Bin): b.incr.toNat = 1 + b.toNat := by
  induction b with
    | zero => simp
    | b₀ b₀ ihb₀ =>
      rw [Bin.toNat]
      rw [Bin.incr]
      rw [Bin.toNat]
      sorry
    | b₁ b₁ ihb₁ =>
      rw [Bin.toNat]
      rw [Bin.incr]
      rw [Bin.toNat]
      rw [ihb₁]
      sorry

def Bin.ofNat: Nat -> Bin
  | .zero => .zero
  | .succ n => (ofNat n).incr

theorem Bin.natBinNat (n: Nat): (Bin.ofNat n).toNat = n := by
  induction n with
    | zero => rfl
    | succ n ihₙ =>
      rw [Bin.ofNat]
      rw [Bin.toNatPreservesIncr]
      rw [ihₙ]
      rw [Nat.succ_eq_add_one]
      rw [Nat.add_comm]

theorem Nat.doubleIncr (n: Nat): n.succ.double = n.double.succ.succ := by
  induction n with
    | zero => rfl
    | succ n ihₙ =>
      rw [ihₙ]
      rw [Nat.doublePlus, Nat.doublePlus]
      rw [Nat.add_succ, Nat.add_succ, Nat.succ_add, ← Nat.succ_eq_add_one, Nat.succ_add]

def Bin.double: Bin → Bin
  | .zero => .zero
  | .b₀ b => .b₀ b.double
  | .b₁ b => .b₀ b.double.incr

example: (Bin.ofNat 0).double.toNat = 0 := by rfl
example: (Bin.ofNat 1).double.toNat = 2 := by rfl
example: (Bin.ofNat 2).double.toNat = 4 := by rfl
example: (Bin.ofNat 3).double.toNat = 6 := by rfl
example: (Bin.ofNat 4).double.toNat = 8 := by rfl
example: (Bin.ofNat 5).double.toNat = 10 := by rfl
example: (Bin.ofNat 6).double.toNat = 12 := by rfl
example: (Bin.ofNat 7).double.toNat = 14 := by rfl

theorem Bin.doubleIncr (b: Bin): b.incr.double = b.double.incr.incr := by
  induction b with
    | zero => rfl
    | b₀ b₀ _ => simp [Bin.incr, Bin.double]
    | b₁ b₁ ihb₁ =>
      simp [Bin.incr, Bin.double]
      rw [ihb₁]

def Bin.normalize: Bin → Bin
  | .zero => .zero
  | .b₀ b => .b₀ b.normalize
  | .b₁ b => .b₁ b.normalize

theorem Bin.binDoubleMul2 (b: Bin): b.double.toNat = 2 * b.toNat := by
  induction b with
    | zero =>
      simp [Bin.toNat, Bin.double, Nat.mul_zero]
    | b₀ b₀ ihb₀ =>
      simp [Bin.toNat, Bin.double, ihb₀]
    | b₁ b₁ ihb₁ =>
      sorry
      -- rw [
      --   Bin.double,
      --   Bin.toNat,
      --   Bin.toNat,
      --   ← ihb₁,
      -- ]


theorem Bin.binNatBin (b: Bin): Bin.ofNat b.toNat = b := by
  induction b with
    | zero => rfl
    | b₀ b₀ ihb₀ => sorry
    | b₁ b₁ ihb₁ => sorry
