/-
# Proof By Induction
-/

/-
## Separate Compilation
-/

import SoftwareFoundations.LogicalFoundations.Basics

namespace SoftwareFoundations.LogicalFoundations.Induction
  open Basics

  /-
  ## Proof By Induction

  Some of the proofs have to reach into the theorems defined by the Prelude to
  do some of the low-level manipulation required to get the terms into a state
  where we can perform induction (without resorting to `simp`).  I've attempted
  to keep this to a minimum so that it doesn't distract from the more important
  recursive nature of the proof.
  -/

  @[reducible]
  def _root_.Nat.double: Nat → Nat
    | .zero => .zero
    | .succ n => n.double.succ.succ

  namespace Term
    theorem Nat.zero_add: ∀ n: Nat, 0 + n = n
      | .zero => rfl
      | .succ n =>
        have ih := zero_add n
        calc 0 + n.succ
          _ = (0 + n).succ := Nat.add_succ 0 n
          _ = n.succ       := congrArg Nat.succ ih

    theorem Nat.minus_self: ∀ n: Nat, n - n = 0
      | .zero => rfl
      | .succ n =>
        have ih := minus_self n
        calc n.succ - n.succ
          _ = n - n := Nat.succ_sub_succ n n
          _ = 0     := ih

    theorem Nat.zero_mul: ∀ n: Nat, 0 * n = 0
      | .zero => rfl
      | .succ n =>
        have ih := zero_mul n
        calc 0 * n.succ
          _ = 0 * n + 0 := Nat.mul_succ 0 n
          _ = 0 * n     := Nat.add_zero (0 * n)
          _ = 0         := ih

    theorem Nat.succ_add: ∀ n₁ n₂: Nat, n₁.succ + n₂ = (n₁ + n₂).succ
      | _, .zero => rfl
      | n₁, .succ n₂ =>
        have ih := succ_add n₁ n₂
        calc n₁.succ + n₂.succ
          _ = (n₁.succ + n₂).succ := rfl
          _ = (n₁ + n₂).succ.succ := congrArg Nat.succ ih

    theorem Nat.add_comm: ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁
      | n₁, .zero =>
        calc n₁ + 0
          _ = n₁     := Nat.add_zero n₁
          _ = 0 + n₁ := Eq.symm (Nat.zero_add n₁)
      | n₁, .succ n₂ =>
        have ih := add_comm n₁ n₂
        calc n₁ + n₂.succ
          _ = (n₁ + n₂).succ := Nat.add_succ n₁ n₂
          _ = (n₂ + n₁).succ := congrArg Nat.succ ih
          _ = n₂.succ + n₁   := Eq.symm (Nat.succ_add n₂ n₁)

      theorem Nat.add_assoc: ∀ n₁ n₂ n₃: Nat, n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃
        | n₁, .zero, n₃ =>
          calc n₁ + (0 + n₃)
            _ = n₁ + n₃ := congrArg (Nat.add n₁) (Nat.zero_add n₃)
            _ = (n₁ + 0) + n₃ := congr (congrArg Nat.add (Eq.symm (Nat.add_zero n₁))) rfl
        | n₁, .succ n₂, n₃ =>
          have ih := add_assoc n₁ n₂ n₃
          calc n₁ + (n₂.succ + n₃)
            _ = n₁ + (n₂ + n₃).succ   := congrArg (Nat.add n₁) (Nat.succ_add n₂ n₃)
            _ = (n₁ + (n₂ + n₃)).succ := Nat.add_succ n₁ (n₂ + n₃)
            _ = ((n₁ + n₂) + n₃).succ := congrArg Nat.succ ih
            _ = (n₁ + n₂).succ + n₃   := Eq.symm (Nat.succ_add (n₁ + n₂) n₃)
            _ = (n₁ + n₂.succ) + n₃   := congr (congrArg Nat.add (Eq.symm (Nat.add_succ n₁ n₂))) rfl

      theorem Nat.double_plus: ∀ n: Nat, n.double = n + n
        | .zero => rfl
        | .succ n =>
          have ih := double_plus n
          calc n.succ.double
            _ = n.double.succ.succ := rfl
            _ = (n + n).succ.succ  := congrArg Nat.succ (congrArg Nat.succ ih)
            _ = (n.succ + n).succ  := congrArg Nat.succ (Eq.symm (Nat.succ_add n n))
            _ = n.succ + n.succ    := Eq.symm (Nat.add_succ n.succ n)

      theorem Nat.eqb_refl: ∀ n: Nat, n.eqb n = true
        | .zero => rfl
        | .succ n =>
          have ih := eqb_refl n
          calc n.succ.eqb n.succ
            _ = n.eqb n := rfl
            _ = true    := ih

      theorem Nat.even_succ: ∀ n: Nat, n.succ.even? = n.even?.neg
        | .zero => rfl
        | .succ n =>
          have ih := even_succ n
          calc n.succ.succ.even?
            _ = n.even? := rfl
            _ = n.succ.even?.neg := sorry
  end Term

  namespace Tactic
    @[scoped simp]
    theorem Nat.zero_add (n: Nat): 0 + n = n := by
      induction n with
        | zero => rfl
        | succ n ih => simp [ih]

    @[scoped simp]
    theorem Nat.minus_self (n: Nat): n - n = 0 := by
      induction n with
        | zero => rfl
        | succ n ih => simp [ih]

    @[scoped simp]
    theorem Nat.zero_mul (n: Nat): 0 * n = 0 := by
      induction n with
        | zero => rfl
        | succ n ih => simp [ih]

    theorem Nat.succ_add (n₁ n₂: Nat): n₁.succ + n₂ = (n₁ + n₂).succ := by
      induction n₂ with
        | zero => rfl
        | succ n₂ ih => simp [Nat.add_succ, ih]

    theorem Nat.add_comm (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ := by
      induction n₂ with
        | zero => simp
        | succ n₂ ih => simp [Nat.add_succ, ih, Nat.succ_add]

    theorem Nat.add_assoc (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃ := by
      induction n₂ with
      | zero => simp
      | succ n₂ ih => simp [Nat.add_succ, Nat.succ_add, ih]

    theorem Nat.double_plus (n: Nat): n.double = n + n := by
      induction n with
        | zero => rfl
        | succ n ih => simp [ih, Nat.add_succ, Nat.succ_add]

    theorem Nat.eqb_refl (n: Nat): n.eqb n = true := by
      induction n with
        | zero => rfl
        | succ n ih => simp [ih]

    theorem Nat.even_succ (n: Nat): n.succ.even? = n.even?.neg := by
      induction n with
        | zero => rfl
        | succ n ih => sorry
  end Tactic

  namespace Blended
    @[scoped simp]
    theorem Nat.zero_add: ∀ n: Nat, 0 + n = n
      | .zero => by rfl
      | .succ n => by
        have ih := zero_add n
        simp [ih]

    @[scoped simp]
    theorem Nat.minus_self: ∀ n: Nat, n - n = 0
      | .zero => by rfl
      | .succ n => by
        have ih := minus_self n
        simp [ih]

    @[scoped simp]
    theorem Nat.zero_mul: ∀ n: Nat, 0 * n = 0
      | .zero => by rfl
      | .succ n => by
        have ih := zero_mul n
        simp [ih]

    theorem Nat.succ_add: ∀ n₁ n₂: Nat, n₁.succ + n₂ = (n₁ + n₂).succ
      | _, .zero => rfl
      | n₁, .succ n₂ =>
        have ih := succ_add n₁ n₂
        calc n₁.succ + n₂.succ
          _ = (n₁.succ + n₂).succ := by rfl
          _ = (n₁ + n₂).succ.succ := by rw [ih]

    theorem Nat.add_comm: ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁
      | n₁, .zero => by simp
      | n₁, .succ n₂ =>
        have ih := add_comm n₁ n₂
        calc n₁ + n₂.succ
          _ = (n₁ + n₂).succ := by simp [Nat.add_succ]
          _ = (n₂ + n₁).succ := by rw [ih]
          _ = n₂.succ + n₁   := by simp [Nat.succ_add]

    theorem Nat.add_assoc: ∀ n₁ n₂ n₃: Nat, n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃
      | n₁, .zero, n₃ => by simp
      | n₁, .succ n₂, n₃ =>
        have ih := add_assoc n₁ n₂ n₃
        calc n₁ + (n₂.succ + n₃)
          _ = (n₁ + (n₂ + n₃)).succ := by simp [Nat.add_succ, Nat.succ_add]
          _ = ((n₁ + n₂) + n₃).succ := by rw [ih]
          _ = (n₁ + n₂.succ) + n₃   := by simp [Nat.add_succ, Nat.succ_add]

    theorem Nat.double_plus: ∀ n: Nat, n.double = n + n
      | .zero => rfl
      | .succ n =>
        have ih := double_plus n
        calc n.succ.double
          _ = n.double.succ.succ := by rfl
          _ = (n + n).succ.succ  := by rw [ih]
          _ = n.succ + n.succ    := by simp [Nat.add_succ, Nat.succ_add]

    theorem Nat.eqb_refl: ∀ n: Nat, n.eqb n = true
      | .zero => rfl
      | .succ n =>
        have ih := eqb_refl n
        calc n.succ.eqb n.succ
          _ = n.eqb n := by rfl
          _ = true    := by rw [ih]

    theorem Nat.even_succ: ∀ n: Nat, n.succ.even? = n.even?.neg
      | .zero => rfl
      | .succ n =>
        have ih := even_succ n
        calc n.succ.succ.even?
          _ = n.even?          := by rfl
          _ = n.succ.even?.neg := sorry
  end Blended

  /-
  ## Proofs within Proofs
  -/

  namespace Term
    example {n₁ n₂: Nat}: (n₁ + 0 + 0) * n₂ = n₁ * n₂ :=
      have h: n₁ + 0 + 0 = n₁ :=
        calc n₁ + 0 + 0
          _ = n₁ + 0 := Nat.add_zero (n₁ + 0)
          _ = n₁     := Nat.add_zero n₁
      calc (n₁ + 0 + 0) * n₂
        _ = n₁ * n₂ := congr (congrArg Nat.mul h) rfl

    example {n₁ n₂ n₃ n₄: Nat}: (n₁ + n₂) + (n₃ + n₄) = (n₂ + n₁) + (n₃ + n₄) :=
      have h: n₁ + n₂ = n₂ + n₁ := Nat.add_comm n₁ n₂
      calc (n₁ + n₂) + (n₃ + n₄)
        _ = (n₂ + n₁) + (n₃ + n₄) := congr (congrArg Nat.add h) rfl
  end Term

  namespace Tactic
    example {n₁ n₂: Nat}: (n₁ + 0 + 0) * n₂ = n₁ * n₂ := by
      have h: n₁ + 0 + 0 = n₁ := by simp
      rw [h]

    example {n₁ n₂ n₃ n₄: Nat}: (n₁ + n₂) + (n₃ + n₄) = (n₂ + n₁) + (n₃ + n₄) := by
      have h: n₁ + n₂ = n₂ + n₁ := by rw [Nat.add_comm]
      rw [h]
  end Tactic

  namespace Blended
    example {n₁ n₂: Nat}: (n₁ + 0 + 0) * n₂ = n₁ * n₂ :=
      have h: n₁ + 0 + 0 = n₁ := by simp
      calc (n₁ + 0 + 0) * n₂
        _ = n₁ * n₂ := by rw [h]

    example {n₁ n₂ n₃ n₄: Nat}: (n₁ + n₂) + (n₃ + n₄) = (n₂ + n₁) + (n₃ + n₄) :=
      have h: n₁ + n₂ = n₂ + n₁ := by rw [Nat.add_comm]
      calc (n₁ + n₂) + (n₃ + n₄)
        _ = (n₂ + n₁) + (n₃ + n₄) := by rw [h]
  end Blended

  /-
  ## Formal vs. Informal Proofs
  -/

  /-
  ### Informal proof of `Nat.add_comm`

  TODO
  -/

  /-
  ### Informal proof of `Nat.add_assoc`

  TODO
  -/

  /-
  ## More Exercises
  -/

  namespace Term
    -- TODO: Why is this needed here to make the `Nat.succ_neqb_zero` and the
    -- `Nat.zero_neqb_succ` theorems see the theorems they operate on?  This
    -- must be a bug on my end.
    open Basics.Term

    theorem Nat.add_swap_left (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) :=
      have h: n₁ + n₂ = n₂ + n₁ := Nat.add_comm n₁ n₂
      calc n₁ + (n₂ + n₃)
        _ = (n₁ + n₂) + n₃ := Nat.add_assoc n₁ n₂ n₃
        _ = (n₂ + n₁) + n₃ := congr (congrArg Nat.add h) rfl
        _ = n₂ + (n₁ + n₃) := Eq.symm (Nat.add_assoc n₂ n₁ n₃)

    theorem Nat.mul_comm: ∀ n₁ n₂: Nat, n₁ * n₂ = n₂ * n₁
      | n₁, .zero =>
        calc n₁ * 0
          _ = 0 := Nat.mul_zero n₁
          _ = 0 * n₁ := Eq.symm (Nat.zero_mul n₁)
      | n₁, .succ n₂ =>
        have ih := mul_comm n₁ n₂
        calc n₁ * n₂.succ
          _ = (n₁ * n₂) + n₁ := rfl
          _ = (n₂ * n₁) + n₁ := congr (congrArg Nat.add ih) rfl
          _ = n₂.succ * n₁ := sorry

    theorem Nat.le_add_left: ∀ n₁ n₂ n₃: Nat, n₁.leb n₂ = .true → (n₃ + n₁).leb (n₃ + n₂) = .true
      | n₁, n₂, .zero, h =>
        calc (.zero + n₁).leb (.zero + n₂)
          _ = n₁.leb n₂ := congr (congrArg Nat.leb (Nat.zero_add n₁)) (Nat.zero_add n₂)
          _ = .true     := h
      | n₁, n₂, .succ n₃, h =>
        have ih := le_add_left n₁ n₂ n₃ h
        calc (n₃.succ + n₁).leb (n₃.succ + n₂)
          _ = (n₃ + n₁).succ.leb (n₃ + n₂).succ := congr (congrArg Nat.leb (Nat.succ_add n₃ n₁)) (Nat.succ_add n₃ n₂)
          _ = (n₃ + n₁).leb (n₃ + n₂)           := rfl
          _ = .true                             := ih

    theorem Nat.leb_refl: ∀ n: Nat, n.leb n = .true
      | .zero => rfl
      | .succ n =>
        have ih := leb_refl n
        calc n.succ.leb n.succ
          _ = n.leb n := rfl
          _ = .true   := ih

    theorem Nat.succ_neqb_zero (n: Nat): n.succ.eqb 0 = .false :=
      calc n.succ.eqb 0
        _ = (n + 1).eqb 0 := congr (congrArg Nat.eqb (Eq.symm (Nat.add_one_eq_succ n))) rfl
        _ = .false        := Nat.add_one_neqb_zero n

    theorem Bool.and_false: ∀ b: Basics.Bool, (b && .false) = .false
      | .true => rfl
      | .false => rfl

    theorem Nat.zero_neqb_succ (n: Nat): (0).eqb n.succ = .false :=
      calc (0).eqb n.succ
        _ = (0).eqb (n + 1) := congrArg (Nat.eqb 0) (Eq.symm (Nat.add_one_eq_succ n))
        _ = .false          := Nat.zero_neqb_add_one n

    theorem Nat.one_mul: ∀ n: Nat, 1 * n = n
      | .zero => rfl
      | .succ n =>
        have ih := one_mul n
        calc 1 * n.succ
          _ = (1 * n) + 1 := rfl
          _ = n + 1       := congr (congrArg Nat.add ih) rfl
          _ = n.succ      := Nat.add_one_eq_succ n

    example: ∀ b₁ b₂: Basics.Bool, ((b₁ && b₂) || (!b₁ || !b₂)) = .true
      | .true, .true => rfl
      | .true, .false => rfl
      | .false, _ => rfl

    theorem Nat.add_mul: ∀ n₁ n₂ n₃: Nat, (n₁ + n₂) * n₃ = (n₁ * n₃) + (n₂ * n₃)
      | n₁, n₂, .zero =>
        calc (n₁ + n₂) * 0
          _ = 0                   := Nat.mul_zero (n₁ + n₂)
          _ = 0 + 0               := Eq.symm (Nat.add_zero 0)
          _ = (n₁ * 0) + (n₂ * 0) := congr (congrArg Nat.add (Eq.symm (Nat.mul_zero n₁))) (Eq.symm (Nat.mul_zero n₂))
      | n₁, n₂, .succ n₃ =>
        have ih := add_mul n₁ n₂ n₃
        calc (n₁ + n₂) * n₃.succ
          _ = ((n₁ + n₂) * n₃) + (n₁ + n₂)        := rfl
          _ = ((n₁ * n₃) + (n₂ * n₃)) + (n₁ + n₂) := congr (congrArg Nat.add ih) rfl
          _ = ((n₂ * n₃) + (n₁ * n₃)) + (n₁ + n₂) := congr (congrArg Nat.add (Nat.add_comm (n₁ * n₃) (n₂ * n₃))) rfl
          _ = (n₂ * n₃) + ((n₁ * n₃) + (n₁ + n₂)) := Eq.symm (Nat.add_assoc (n₂ * n₃) (n₁ * n₃) (n₁ + n₂))
          _ = (n₂ * n₃) + (((n₁ * n₃) + n₁) + n₂) := congrArg (Nat.add (n₂ * n₃)) (Nat.add_assoc (n₁ * n₃) n₁ n₂)
          _ = (n₂ * n₃) + ((n₁ * n₃.succ) + n₂)   := rfl
          _ = (n₁ * n₃.succ) + ((n₂ * n₃) + n₂)   := Nat.add_swap_left (n₂ * n₃) (n₁ * n₃.succ) n₂
          _ = (n₁ * n₃.succ) + (n₂ * n₃.succ)     := rfl

    theorem Nat.mul_assoc: ∀ n₁ n₂ n₃: Nat, n₁ * (n₂ * n₃) = (n₁ * n₂) * n₃
      | n₁, .zero, n₃ =>
        calc n₁ * (0 * n₃)
          _ = n₁ * 0        := congrArg (Nat.mul n₁) (Nat.zero_mul n₃)
          _ = 0             := Nat.mul_zero n₁
          _ = 0 * n₃        := Eq.symm (Nat.zero_mul n₃)
          _ = (n₁ * 0) * n₃ := congr (congrArg Nat.mul (Eq.symm (Nat.mul_zero n₁))) rfl
      | n₁, .succ n₂, n₃ =>
        have ih := mul_assoc n₁ n₂ n₃
        calc n₁ * (n₂.succ * n₃)
          _ = n₁ * (n₃ * n₂.succ)          := congrArg (Nat.mul n₁) (Nat.mul_comm n₂.succ n₃)
          _ = n₁ * ((n₃ * n₂) + n₃)        := rfl
          _ = n₁ * ((n₂ * n₃) + n₃)        := congrArg (Nat.mul n₁) (congr (congrArg Nat.add (Nat.mul_comm n₃ n₂)) rfl)
          _ = ((n₂ * n₃) + n₃) * n₁        := Nat.mul_comm n₁ ((n₂ * n₃) + n₃)
          _ = ((n₂ * n₃) * n₁) + (n₃ * n₁) := Nat.add_mul (n₂ * n₃) n₃ n₁
          _ = (n₁ * (n₂ * n₃)) + (n₃ * n₁) := congr (congrArg Nat.add (Nat.mul_comm (n₂ * n₃) n₁)) rfl
          _ = ((n₁ * n₂) * n₃) + (n₃ * n₁) := congr (congrArg Nat.add ih) rfl
          _ = ((n₁ * n₂) * n₃) + (n₁ * n₃) := congrArg (Nat.add ((n₁ * n₂) * n₃)) (Nat.mul_comm n₃ n₁)
          _ = ((n₁ * n₂) + n₁) * n₃        := Eq.symm (Nat.add_mul (n₁ * n₂) n₁ n₃)
          _ = (n₁ * n₂.succ) * n₃          := rfl
  end Term

  namespace Tactic
    open Basics.Tactic

    theorem Nat.add_swap_left (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) := by
      have h: n₁ + n₂ = n₂ + n₁ := Nat.add_comm n₁ n₂
      simp [Nat.add_assoc, h]

    theorem Nat.mul_comm (n₁ n₂: Nat): n₁ * n₂ = n₂ * n₁ := by
      induction n₂ with
        | zero => simp
        | succ n₂ ih =>
          calc n₁ * n₂.succ
            _ = (n₁ * n₂) + n₁ := by rfl
            _ = (n₂ * n₁) + n₁ := by rw [ih]
            _ = n₂.succ * n₁ := sorry

    theorem Nat.le_add_left (n₁ n₂ n₃: Nat) (h: n₁.leb n₂ = .true): (n₃ + n₁).leb (n₃ + n₂) = .true := by
      induction n₃ with
        | zero => simp [h]
        | succ _ ih => simp [Nat.succ_add, ih]

    theorem Nat.leb_refl (n: Nat): n.leb n = .true := by
      induction n with
        | zero => rfl
        | succ _ ih => rw [ih]

    theorem Nat.succ_neqb_zero (n: Nat): n.succ.eqb 0 = .false := by
      simp

    theorem Bool.and_false: ∀ b: Basics.Bool, (b && .false) = .false := by
      intro
        | .true => rfl
        | .false => rfl

    theorem Nat.zero_neqb_succ (n: Nat): (0).eqb n.succ = .false := by
      simp

    theorem Nat.one_mul (n: Nat): 1 * n = n := by
      induction n with
        | zero => rfl
        | succ n ih =>
          calc 1 * n.succ
            _ = (1 * n) + 1 := by rfl
            _ = n + 1       := by rw [ih]

    example: ∀ b₁ b₂: Basics.Bool, ((b₁ && b₂) || (!b₁ || !b₂)) = .true := by
      intro
        | .true, .true => rfl
        | .true, .false => rfl
        | .false, _ => rfl

    theorem Nat.add_mul (n₁ n₂ n₃: Nat): (n₁ + n₂) * n₃ = (n₁ * n₃) + (n₂ * n₃) := by
      induction n₃ with
        | zero => simp
        | succ n₃ ih =>
          calc (n₁ + n₂) * n₃.succ
            _ = ((n₁ + n₂) * n₃) + (n₁ + n₂)        := by rfl
            _ = ((n₁ * n₃) + (n₂ * n₃)) + (n₁ + n₂) := by rw [ih]
            _ = (n₂ * n₃) + (((n₁ * n₃) + n₁) + n₂) := by simp [Nat.mul, Nat.add_assoc, Nat.add_comm]
            _ = (n₂ * n₃) + ((n₁ * n₃.succ) + n₂)   := by rfl
            _ = (n₁ * n₃.succ) + ((n₂ * n₃) + n₂)   := by simp [Nat.add_swap_left]
            _ = (n₁ * n₃.succ) + (n₂ * n₃.succ)     := by rfl

    theorem Nat.mul_assoc (n₁ n₂ n₃: Nat): n₁ * (n₂ * n₃) = (n₁ * n₂) * n₃ := by
      induction n₂ with
        | zero => simp
        | succ n₂ ih =>
          calc n₁ * (n₂.succ * n₃)
            _ = n₁ * (n₃ * n₂.succ)          := by simp [Nat.mul_comm]
            _ = n₁ * ((n₃ * n₂) + n₃)        := by rfl
            _ = (n₁ * (n₂ * n₃)) + (n₃ * n₁) := by rw [Nat.mul_comm n₂ n₃, Nat.mul_comm, Nat.add_mul, Nat.mul_comm]
            _ = ((n₁ * n₂) * n₃) + (n₃ * n₁) := by rw [ih]
            _ = ((n₁ * n₂) + n₁) * n₃        := by simp [Nat.add_mul, Nat.mul_comm n₃ n₁]
            _ = (n₁ * n₂.succ) * n₃          := by rfl
  end Tactic

  namespace Blended
    open Basics.Blended

    theorem Nat.add_swap_left (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = n₂ + (n₁ + n₃) :=
      have h: n₁ + n₂ = n₂ + n₁ := Nat.add_comm n₁ n₂
      calc n₁ + (n₂ + n₃)
        _ = (n₁ + n₂) + n₃ := by simp [Nat.add_assoc]
        _ = (n₂ + n₁) + n₃ := by rw [h]
        _ = n₂ + (n₁ + n₃) := by simp [Nat.add_assoc]

    theorem Nat.mul_comm: ∀ n₁ n₂: Nat, n₁ * n₂ = n₂ * n₁
      | _, .zero => by simp
      | n₁, .succ n₂ =>
        have ih := mul_comm n₁ n₂
        calc n₁ * n₂.succ
          _ = (n₁ * n₂) + n₁ := by rfl
          _ = (n₂ * n₁) + n₁ := by rw [ih]
          _ = n₂.succ * n₁ := sorry

    theorem Nat.le_add_left: ∀ n₁ n₂ n₃: Nat, n₁.leb n₂ = .true → (n₃ + n₁).leb (n₃ + n₂) = .true
      | _, _, .zero, h => by simp [h]
      | n₁, n₂, .succ n₃, h =>
        have ih := le_add_left n₁ n₂ n₃ h
        calc (n₃.succ + n₁).leb (n₃.succ + n₂)
          _ = (n₃ + n₁).leb (n₃ + n₂) := by simp [Nat.succ_add]
          _ = .true                   := by rw [ih]

    theorem Nat.leb_refl: ∀ n: Nat, n.leb n = .true
      | .zero => by rfl
      | .succ n =>
        have ih := leb_refl n
        calc n.succ.leb n.succ
          _ = .true := by rw [ih]

    theorem Nat.succ_neqb_zero (n: Nat): n.succ.eqb 0 = .false :=
      calc n.succ.eqb 0
        _ = .false := by simp

    theorem Bool.and_false: ∀ b: Basics.Bool, (b && .false) = .false
      | .true => by rfl
      | .false => by rfl

    theorem Nat.zero_neqb_succ (n: Nat): (0).eqb n.succ = .false :=
      calc (0).eqb n.succ
        _ = .false := by simp

    theorem Nat.one_mul: ∀ n: Nat, 1 * n = n
      | .zero => by rfl
      | .succ n =>
        have ih := one_mul n
        calc 1 * n.succ
          _ = (1 * n) + 1 := by rfl
          _ = n + 1       := by rw [ih]

    example: ∀ b₁ b₂: Basics.Bool, ((b₁ && b₂) || (!b₁ || !b₂)) = .true
      | .true, .true => by rfl
      | .true, .false => by rfl
      | .false, _ => by rfl

    theorem Nat.add_mul: ∀ n₁ n₂ n₃: Nat, (n₁ + n₂) * n₃ = (n₁ * n₃) + (n₂ * n₃)
      | _, _, .zero => by simp
      | n₁, n₂, .succ n₃ =>
        have ih := add_mul n₁ n₂ n₃
        calc (n₁ + n₂) * n₃.succ
          _ = ((n₁ + n₂) * n₃) + (n₁ + n₂)        := by rfl
          _ = ((n₁ * n₃) + (n₂ * n₃)) + (n₁ + n₂) := by rw [ih]
          _ = (n₂ * n₃) + (((n₁ * n₃) + n₁) + n₂) := by simp [Nat.mul, Nat.add_assoc, Nat.add_comm]
          _ = (n₂ * n₃) + ((n₁ * n₃.succ) + n₂)   := by rfl
          _ = (n₁ * n₃.succ) + ((n₂ * n₃) + n₂)   := by simp [Nat.add_swap_left]
          _ = (n₁ * n₃.succ) + (n₂ * n₃.succ)     := by rfl

    theorem Nat.mul_assoc: ∀ n₁ n₂ n₃: Nat, n₁ * (n₂ * n₃) = (n₁ * n₂) * n₃
      | _, .zero, _ => by simp
      | n₁, .succ n₂, n₃ =>
        have ih := mul_assoc n₁ n₂ n₃
        calc n₁ * (n₂.succ * n₃)
          _ = n₁ * (n₃ * n₂.succ)          := by simp [Nat.mul_comm]
          _ = n₁ * ((n₃ * n₂) + n₃)        := by rfl
          _ = (n₁ * (n₂ * n₃)) + (n₃ * n₁) := by rw [Nat.mul_comm n₂ n₃, Nat.mul_comm, Nat.add_mul, Nat.mul_comm]
          _ = ((n₁ * n₂) * n₃) + (n₃ * n₁) := by rw [ih]
          _ = ((n₁ * n₂) + n₁) * n₃        := by simp [Nat.add_mul, Nat.mul_comm n₃ n₁]
          _ = (n₁ * n₂.succ) * n₃          := by rfl
  end Blended

  /-
  ## Nat to Bin and Back to Nat
  -/

  def _root_.Nat.toBin: Nat → Bin
    | .zero => .nil
    | .succ n => n.toBin.incr

  namespace Term
    open Basics.Term

    theorem Bin.toNat.preserve_incr: ∀ b: Bin, b.incr.toNat = 1 + b.toNat
      | .nil | .zero _ | .one .nil => rfl
      | .one (.zero b) =>
        have ih := preserve_incr b.zero
        calc b.zero.one.incr.toNat
          _ = b.zero.incr.zero.toNat := rfl
          _ = 2 * b.zero.incr.toNat  := rfl
          _ = 2 * (1 + b.zero.toNat) := congrArg (Nat.mul 2) ih
          _ = (1 + b.zero.toNat) * 2 := Nat.mul_comm 2 (1 + b.zero.toNat)
          _ = 2 + (b.zero.toNat * 2) := Nat.add_mul 1 b.zero.toNat 2
          _ = 2 + (2 * b.zero.toNat) := congrArg (Nat.add 2) (Nat.mul_comm b.zero.toNat 2)
          _ = 2 + b.zero.zero        := rfl
          _ = (1 + 1) + b.zero.zero  := rfl
          _ = 1 + (1 + b.zero.zero)  := Eq.symm (Nat.add_assoc 1 1 b.zero.zero)
          _ = 1 + b.zero.one.toNat   := rfl
      | .one (.one b) =>
        have ih := preserve_incr b.one
        calc b.one.one.incr.toNat
          _ = b.one.incr.zero.toNat := rfl
          _ = 2 * b.one.incr.toNat  := rfl
          _ = 2 * (1 + b.one.toNat) := congrArg (Nat.mul 2) ih
          _ = (1 + b.one.toNat) * 2 := Nat.mul_comm 2 (1 + b.one.toNat)
          _ = 2 + (b.one.toNat * 2) := Nat.add_mul 1 b.one.toNat 2
          _ = 2 + (2 * b.one.toNat) := congrArg (Nat.add 2) (Nat.mul_comm b.one.toNat 2)
          _ = 2 + b.one.zero        := rfl
          _ = (1 + 1) + b.one.zero  := rfl
          _ = 1 + (1 + b.one.zero)  := Eq.symm (Nat.add_assoc 1 1 b.one.zero)
          _ = 1 + b.one.one.toNat   := rfl

    theorem Nat.toBin.to_nat: ∀ n: Nat, n.toBin.toNat = n
      | .zero => rfl
      | .succ n =>
        have ih := to_nat n
        calc n.succ.toBin.toNat
          _ = n.toBin.incr.toNat := rfl
          _ = 1 + n.toBin.toNat  := Bin.toNat.preserve_incr n.toBin
          _ = 1 + n              := congrArg (Nat.add 1) ih
          _ = n + 1              := Nat.add_comm 1 n
  end Term

  namespace Tactic
    open Basics.Tactic

    theorem Bin.toNat.preserve_incr (b: Bin): b.incr.toNat = 1 + b.toNat := by
      induction b with
        | nil | zero _ _ => rfl
        | one b ih =>
          cases b with
            | nil => rfl
            | zero b =>
              calc b.zero.one.incr.toNat
                _ = 2 * b.zero.incr.toNat  := by rfl
                _ = 2 * (1 + b.zero.toNat) := by rw [ih]
                _ = 2 + (b.zero.toNat * 2) := by rw [Nat.mul_comm, Nat.add_mul]
                _ = 1 + (1 + b.zero.zero)  := by rw [Nat.mul_comm, Nat.add_assoc]
            | one b =>
              calc b.one.one.incr.toNat
                _ = 2 * b.one.incr.toNat  := by rfl
                _ = 2 * (1 + b.one.toNat) := by rw [ih]
                _ = 2 + (b.one.toNat * 2) := by rw [Nat.mul_comm, Nat.add_mul]
                _ = 1 + (1 + b.one.zero)  := by rw [Nat.mul_comm, Nat.add_assoc]

    theorem Nat.toBin.to_nat (n: Nat): n.toBin.toNat = n := by
      induction n with
        | zero => rfl
        | succ n ih =>
          calc n.succ.toBin.toNat
            _ = n.toBin.incr.toNat := by rfl
            _ = 1 + n.toBin.toNat  := by rw [Bin.toNat.preserve_incr]
            _ = 1 + n              := by rw [ih]
            _ = n + 1              := by rw [Nat.add_comm]
  end Tactic

  namespace Blended
    open Basics.Blended

    theorem Bin.toNat.preserve_incr: ∀ b: Bin, b.incr.toNat = 1 + b.toNat
      | .nil | .zero _ | .one .nil => by rfl
      | .one (.zero b) =>
        have ih := preserve_incr b.zero
        calc b.zero.one.incr.toNat
          _ = 2 * b.zero.incr.toNat  := by rfl
          _ = 2 * (1 + b.zero.toNat) := by rw [ih]
          _ = 2 + (b.zero.toNat * 2) := by rw [Nat.mul_comm, Nat.add_mul]
          _ = 1 + (1 + b.zero.zero)  := by rw [Nat.mul_comm, Nat.add_assoc]
      | .one (.one b) =>
        have ih := preserve_incr b.one
        calc b.one.one.incr.toNat
          _ = 2 * b.one.incr.toNat  := by rfl
          _ = 2 * (1 + b.one.toNat) := by rw [ih]
          _ = 2 + (b.one.toNat * 2) := by rw [Nat.mul_comm, Nat.add_mul]
          _ = 1 + (1 + b.one.zero)  := by rw [Nat.mul_comm, Nat.add_assoc]

    theorem Nat.toBin.to_nat: ∀ n: Nat, n.toBin.toNat = n
      | .zero => rfl
      | .succ n =>
        have ih := to_nat n
        calc n.succ.toBin.toNat
          _ = n.toBin.incr.toNat := by rfl
          _ = 1 + n.toBin.toNat  := by rw [Bin.toNat.preserve_incr]
          _ = 1 + n              := by rw [ih]
          _ = n + 1              := by rw [Nat.add_comm]
  end Blended

  /-
  ## Bin to Nat and Back to Bin (Advanced)
  -/

  @[reducible]
  def _root_.SoftwareFoundations.LogicalFoundations.Basics.Bin.double: Bin → Bin
    | .nil => .nil
    | .zero .nil => .zero .nil
    | b => b.zero

  section
    example: Bin.nil.double = Bin.nil := rfl
  end

  namespace Term
    theorem Nat.double_succ: ∀ n: Nat, n.succ.double = n.double.succ.succ
      | .zero => rfl
      | .succ _ => rfl

    theorem Bin.double_incr: ∀ b: Bin, b.incr.double = b.double.incr.incr
      | .nil
      | .zero .nil | .zero (.zero b) | .zero (.one b)
      | .one .nil | .one (.zero b) => rfl
      | .one (.one b) =>
        have ih := double_incr b.one
        calc b.one.one.incr.double
          _ = b.one.incr.zero.double := rfl
          _ = b.one.one.double.incr.incr := sorry

    theorem Bin.toNat.to_bin: ∀ b: Bin, b.toNat.toBin = b := sorry
  end Term

  namespace Tactic
    theorem Nat.double_succ: ∀ n: Nat, n.succ.double = n.double.succ.succ := by
      intro
        | .zero => rfl
        | .succ _ => rfl

    theorem Bin.double_incr (b: Bin): b.incr.double = b.double.incr.incr := by
      induction b with
        | nil => rfl
        | zero b _ => cases b <;> rfl
        | one b ih =>
          cases b with
            | nil | zero _ => rfl
            | one b =>
              calc b.one.one.incr.double
                _ = b.one.incr.zero.double := rfl
                _ = b.one.one.double.incr.incr := sorry

    theorem Bin.toNat.to_bin: ∀ b: Bin, b.toNat.toBin = b := by
      sorry
  end Tactic

  namespace Blended
    theorem Nat.double_succ: ∀ n: Nat, n.succ.double = n.double.succ.succ
      | .zero => by rfl
      | .succ _ => by rfl

    theorem Bin.double_incr: ∀ b: Bin, b.incr.double = b.double.incr.incr
      | .nil
      | .zero .nil | .zero (.zero b) | .zero (.one b)
      | .one .nil | .one (.zero b) => by rfl
      | .one (.one b) =>
        have ih := double_incr b.one
        calc b.one.one.incr.double
          _ = b.one.incr.zero.double := rfl
          _ = b.one.one.double.incr.incr := sorry

    theorem Bin.toNat.to_bin: ∀ b: Bin, b.toNat.toBin = b := sorry
  end Blended
end SoftwareFoundations.LogicalFoundations.Induction
