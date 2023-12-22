import «SoftwareFoundations».«LogicalFoundations».Basics

/-
# Induction
-/

/-
## Proof By Induction
-/

theorem addZeroRight (n: Nat): n + 0 = n := by simp
theorem minusSelf (n: Nat): n - n = 0 := by simp

/-
#### Exercises
-/

theorem mulZeroRight (n: Nat): n * 0 = 0 := by
  cases n with
    | zero => rfl
    | succ _ => simp

theorem plusNSucc (n₁ n₂: Nat): Nat.succ (n₁ + n₂) = n₁ + (Nat.succ n₂) := by
  cases n₁ with
    | zero => simp
    | succ _ => rfl

theorem addComm (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ := by
  rw [Nat.add_comm]

theorem addAssoc (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃ := by
  rw [Nat.add_assoc]

def Nat.double: Nat → Nat
  | .zero => .zero
  | .succ n => (double n).succ.succ

theorem Nat.doublePlus (n: Nat): n.double = n + n := by
  induction n with
    | zero => rfl
    | succ n ihn =>
      simp [Nat.double, Nat.add_succ]
      rw [ihn]
      rw [Nat.succ_add]

theorem 𝔹.eqRefl (n: Nat): n.eq n := by
  induction n with
    | zero => rfl
    | succ n ihₙ => rw [Nat.eq, ihₙ]

theorem Nat.evenSucc (n: Nat): n.succ.isEven = ¬n.isEven := by
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

theorem Nat.multZeroPlus (n₁ n₂: Nat): (n₁ + 0 + 0) * n₂ = n₁ * n₂ := by
  have h: n₁ + 0 + 0 = n₁ := by simp
  rw [h]

theorem Nat.plusRearrange (n₁ n₂ n₃ n₄: Nat): (n₁ + n₂) + (n₃ + n₄) = (n₂ + n₁) + (n₃ + n₄) := by
  have h: n₁ + n₂ = n₂ + n₁ := by rw [Nat.add_comm]
  rw [h]

/-
## Formal vs. Informal Proofs
-/

/-
#### Exercises
-/

theorem Nat.addShuffle3 (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) := by
  rw [← Nat.add_assoc, Nat.add_comm n₁ n₂, Nat.add_assoc]

theorem Nat.mulComm (n₁ n₂: Nat): n₁ * n₂ = n₂ * n₁ := by
  induction n₁ with
    | zero => simp
    | succ n₁ ihn₁ => rw [Nat.succ_mul, ihn₁, Nat.mul_succ]

theorem Nat.leqCompatL (n₁ n₂ n₃: Nat): n₁.less_eq n₂ → (n₃ + n₁).less_eq (n₃ + n₂) := by
  induction n₃ with
    | zero =>
      intro h
      rw [Nat.zero_add, Nat.zero_add]
      exact h
    | succ n₃ ihn₃ =>
      rw [Nat.succ_add, Nat.succ_add]
      rw [Nat.less_eq]
      exact ihn₃

theorem Nat.lessEqRefl (n₁ n₂: Nat) (h: n₁.less_eq n₂): n₂.less_eq n₂ := by
  sorry

theorem Nat.zeroNeSucc (n: Nat): n ≠ n.succ := by
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
      rw [succ.injEq] at h
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
