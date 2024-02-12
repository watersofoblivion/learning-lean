/-
# More Basic Tactics
-/

import SoftwareFoundations.LogicalFoundations.Poly

namespace SoftwareFoundations.LogicalFoundations.Tactics
  /-
  ## The `apply` Tactic
  -/

  namespace Term
    -- open Poly.Term

    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁ = n₂ :=
      h

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₁ = n₂) (h₂: (n₁ = n₂) → [n₁, n₃] = [n₂, n₄]): [n₁, n₃] = [n₂, n₄] :=
      h₂ h₁

    example {n₁ n₂: Nat} (h₁: (n₁, n₁) = (n₂, n₂)) (h₂: {n₃ n₄: Nat} → (n₃, n₃) = (n₄, n₄) → [n₃] = [n₄]): [n₁] = [n₂] :=
      h₂ h₁

    example {p: Nat} (h₁: {n: Nat} → n.even? = .true → n.succ.even? = .false) (h₂: {n: Nat} → n.even? = .false → n.odd? = .true) (h₃: p.even? = .true): p.succ.odd? = .true :=
      h₂ (h₁ h₃)

    example {n₁ n₂: Nat} (h: n₁ = n₂): n₂ = n₁ :=
      Eq.symm h

    example {l₁ l₂: List α} (h: l₁.reverse = l₂): l₂.reverse = l₁ :=
      calc l₂.reverse
        _ = l₁.reverse.reverse := congrArg List.reverse (Eq.symm h)
        _ = l₁                 := List.reverse_reverse l₁
  end Term

  namespace Tactic
    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁ = n₂ := by
      apply h

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₁ = n₂) (h₂: (n₁ = n₂) → [n₁, n₃] = [n₂, n₄]): [n₁, n₃] = [n₂, n₄] := by
      apply h₂
      · apply h₁

    example {n₁ n₂: Nat} (h₁: (n₁, n₁) = (n₂, n₂)) (h₂: {n₃ n₄: Nat} → (n₃, n₃) = (n₄, n₄) → [n₃] = [n₄]): [n₁] = [n₂] := by
      apply h₂
      · apply h₁

    example {p: Nat} (h₁: {n: Nat} → n.even? = .true → n.succ.even? = .false) (h₂: {n: Nat} → n.even? = .false → n.odd? = .true) (h₃: p.even? = .true): p.succ.odd? = .true := by
      apply h₂
      · apply h₁
        · apply h₃

    example {n₁ n₂: Nat} (h: n₁ = n₂): n₂ = n₁ := by
      apply Eq.symm
      · apply h

    example {l₁ l₂: List α} (h: l₁.reverse = l₂): l₂.reverse = l₁ := by
      rw [← h]
      apply List.reverse_reverse
  end Tactic

  namespace Blended
    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁ = n₂ :=
      h

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₁ = n₂) (h₂: (n₁ = n₂) → [n₁, n₃] = [n₂, n₄]): [n₁, n₃] = [n₂, n₄] :=
      h₂ h₁

    example {n₁ n₂: Nat} (h₁: (n₁, n₁) = (n₂, n₂)) (h₂: {n₃ n₄: Nat} → (n₃, n₃) = (n₄, n₄) → [n₃] = [n₄]): [n₁] = [n₂] :=
      h₂ h₁

    example {p: Nat} (h₁: {n: Nat} → n.even? = .true → n.succ.even? = .false) (h₂: {n: Nat} → n.even? = .false → n.odd? = .true) (h₃: p.even? = .true): p.succ.odd? = .true :=
      h₂ (h₁ h₃)

    example {n₁ n₂: Nat} (h: n₁ = n₂): n₂ = n₁ :=
      Eq.symm h

    example {l₁ l₂: List α} (h: l₁.reverse = l₂): l₂.reverse = l₁ :=
      calc l₂.reverse
        _ = l₁.reverse.reverse := by rw [h]
        _ = l₁                 := List.reverse_reverse l₁

  end Blended

  /-
  ## The `apply with` Tactic

  The examples shown here (in the `Tactic` namespace) don't strictly need the
  value of `b` to be explicitly set.
  -/

  namespace Term
    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] :=
      calc [n₁, n₂]
        _ = [n₃, n₄] := h₁
        _ = [n₅, n₆] := h₂

    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] :=
      trans h₁ h₂

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₂ = n₃.pred.pred) (h₂: n₁ + n₄ = n₂): n₁ + n₄ = n₃.pred.pred :=
      calc n₁ + n₄
        _ = n₂           := h₂
        _ = n₃.pred.pred := h₁
  end Term

  namespace Tactic
    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] := by
      rw [h₁, h₂]

    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] := by
      apply Eq.trans (b := [n₃, n₄])
      · apply h₁
      · apply h₂

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₂ = n₃.pred.pred) (h₂: n₁ + n₄ = n₂): n₁ + n₄ = n₃.pred.pred := by
      apply Eq.trans (b := n₂)
      · apply h₂
      · apply h₁
  end Tactic

  namespace Blended
    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] :=
      calc [n₁, n₂]
        _ = [n₃, n₄] := by rw [h₁]
        _ = [n₅, n₆] := by rw [h₂]

    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] :=
      trans h₁ h₂

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₂ = n₃.pred.pred) (h₂: n₁ + n₄ = n₂): n₁ + n₄ = n₃.pred.pred :=
      calc n₁ + n₄
        _ = n₂           := by rw [h₂]
        _ = n₃.pred.pred := by rw [h₁]
  end Blended

  /-
  ## The `injection` and `contradiction` (Coq's `discriminate`) Tactics
  -/

  namespace Term
    theorem Nat.succ_inj {n₁ n₂: Nat} (h: n₁.succ = n₂.succ): n₁ = n₂ :=
      congrArg Nat.pred h

    example {n₁ n₂ n₃: Nat} (h: [n₁, n₂] = [n₃, n₃]): n₁ = n₂ :=
      have h₁: n₁ = n₃ := sorry
      have h₂: n₂ = n₃ := sorry
      trans h₁ (Eq.symm h₂)

    example {x₁ x₂ x₃: α} {l₁ l₂: List α} (h₁: x₁ :: x₂ :: l₁ = x₃ :: l₂) (h₂: l₂ = x₃ :: l₁): x₁ = x₂ :=
      have h₁: x₁ = x₃ := sorry
      have h₂: x₂ = x₃ := sorry
      trans h₁ (Eq.symm h₂)

    example {n₁ n₂: Nat} (h: false = true): n₁ = n₂ :=
      (nomatch h) |> absurd h |> False.elim

    example {n: Nat} (h: n.succ = 0): 2 + 2 = 5 :=
      (nomatch h) |> absurd h |> False.elim

    example {x₁ x₂ x₃: α} {l₁ l₂: List α} (h: x :: y :: l = []): x = z :=
      (nomatch h) |> absurd h |> False.elim

    example: ∀ n: Nat, (0 == n) = true → n = 0
      | 0,     _ => rfl
      | _ + 1, h => (nomatch h) |> absurd h |> False.elim

    theorem f_equal {x₁ x₂: α} (f: α → β) (h: x₁ = x₂): f x₁ = f x₂ :=
      congrArg f h

    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁.succ = n₂.succ :=
      f_equal Nat.succ h
  end Term

  namespace Tactic
    example {n₁ n₂: Nat} (h: n₁.succ = n₂.succ): n₁ = n₂ := by
      calc n₁
        _ = n₁.succ.pred := by rfl
        _ = n₂.succ.pred := by rw [h]
        _ = n₂           := by rfl

    theorem Nat.succ_inj {n₁ n₂: Nat} (h: n₁.succ = n₂.succ): n₁ = n₂ := by
      injection h

    example {n₁ n₂ n₃: Nat} (h: [n₁, n₂] = [n₃, n₃]): n₁ = n₂ := by
      injection h with h₁ h₂
      injection h₂ with h₃
      rw [h₁, h₃]

    example {x₁ x₂ x₃: α} {l₁ l₂: List α} (h₁: x₁ :: x₂ :: l₁ = x₃ :: l₂) (h₂: l₂ = x₃ :: l₁): x₁ = x₂ := by
      injection h₁ with h₃ h₄
      rw [h₂] at h₄
      injection h₄ with h₅ h₆
      rw [h₃, h₅]

    example {n₁ n₂: Nat} (h: false = true): n₁ = n₂ := by
      contradiction

    example {n: Nat} (h: n.succ = 0): 2 + 2 = 5 := by
      contradiction

    example {x₁ x₂ x₃: α} {l₁ l₂: List α} (h: x :: y :: l = []): x = z := by
      contradiction

    example (n: Nat) (h: (0 == n) = true): n = 0 := by
      cases n with
        | zero => rfl
        | succ _ => contradiction

    theorem f_equal {x₁ x₂: α} (f: α → β) (h: x₁ = x₂): f x₁ = f x₂ := by
      rw [h]

    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁.succ = n₂.succ := by
      apply f_equal
      · apply h
  end Tactic

  namespace Blended
    theorem Nat.succ_inj {n₁ n₂: Nat} (h: n₁.succ = n₂.succ): n₁ = n₂ :=
      congrArg Nat.pred h

    example {n₁ n₂ n₃: Nat} (h: [n₁, n₂] = [n₃, n₃]): n₁ = n₂ :=
      have h₁: n₁ = n₃ := sorry
      have h₂: n₂ = n₃ := sorry
      by rw [h₁, h₂]

    example {x₁ x₂ x₃: α} {l₁ l₂: List α} (h₁: x₁ :: x₂ :: l₁ = x₃ :: l₂) (h₂: l₂ = x₃ :: l₁): x₁ = x₂ :=
      have h₁: x₁ = x₃ := sorry
      have h₂: x₂ = x₃ := sorry
      by rw [h₁, h₂]

    example {n₁ n₂: Nat} (h: false = true): n₁ = n₂ := by
      contradiction

    example {n: Nat} (h: n.succ = 0): 2 + 2 = 5 := by
      contradiction

    example {x₁ x₂ x₃: α} {l₁ l₂: List α} (h: x :: y :: l = []): x = z := by
      contradiction

    example: ∀ n: Nat, (0 == n) = true → n = 0
      | 0,     _ => by rfl
      | _ + 1, h => by contradiction

    theorem f_equal {x₁ x₂: α} (f: α → β) (h: x₁ = x₂): f x₁ = f x₂ := by
      rw [h]

    example {n₁ n₂: Nat} (h: n₁ = n₂): n₁.succ = n₂.succ :=
      f_equal Nat.succ h
  end Blended

  /-
  ## Using Tactics on Hypotheses
  -/

  namespace Term
    example {n₁ n₂: Nat} {b: Bool} (h: (n₁.succ == n₂.succ) = b): (n₁ == n₂) = b :=
      h

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₁ = n₂ → n₃ = n₄) (h₂: n₂ = n₁): n₄ = n₃ :=
      have h: n₃ = n₄ :=
        h₂ |> Eq.symm |> h₁
      Eq.symm h
  end Term

  namespace Tactic
    example {n₁ n₂: Nat} {b: Bool} (h: (n₁.succ == n₂.succ) = b): (n₁ == n₂) = b := by
      apply h

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₁ = n₂ → n₃ = n₄) (h₂: n₂ = n₁): n₄ = n₃ := by
      have h: n₃ = n₄ := by
        have h: n₁ = n₂ := by
          apply Eq.symm h₂
        apply h₁ h
      apply Eq.symm h
  end Tactic

  namespace Blended
    example {n₁ n₂: Nat} {b: Bool} (h: (n₁.succ == n₂.succ) = b): (n₁ == n₂) = b :=
      h

    example {n₁ n₂ n₃ n₄: Nat} (h₁: n₁ = n₂ → n₃ = n₄) (h₂: n₂ = n₁): n₄ = n₃ :=
      h₂ |> Eq.symm |> h₁ |> Eq.symm
  end Blended

  /-
  ## Specializing Hypotheses
  -/

  namespace Term
    example {n₁: Nat} (h: (n₂: Nat) → n₂ * n₁ = 0): n₁ = 0 :=
      calc n₁
        _ = 1 * n₁ := Eq.symm (Nat.one_mul n₁)
        _ = 0      := h 1

    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] :=
      have h := Eq.trans (b := [n₃, n₄])
      h h₁ h₂
  end Term

  namespace Tactic
    example {n₁: Nat} (h: (n₂: Nat) → n₂ * n₁ = 0): n₁ = 0 := by
      rw [← Nat.one_mul n₁, h 1]

    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] := by
      have h {a c: List Nat}: a = [n₃, n₄] → [n₃, n₄] = c → a = c := Eq.trans (b := [n₃, n₄])
      apply h
      · apply h₁
      · apply h₂
  end Tactic

  namespace Blended
    example {n₁: Nat} (h: (n₂: Nat) → n₂ * n₁ = 0): n₁ = 0 :=
      calc n₁
        _ = 1 * n₁ := by rw [Nat.one_mul]
        _ = 0      := by rw [h 1]

    example {n₁ n₂ n₃ n₄ n₅ n₆: Nat} (h₁: [n₁, n₂] = [n₃, n₄]) (h₂: [n₃, n₄] = [n₅, n₆]): [n₁, n₂] = [n₅, n₆] :=
      have h := Eq.trans (b := [n₃, n₄])
      h h₁ h₂
  end Blended

  /-
  ## Varying the Inductive Hypothesis
  -/

  namespace Term
    example: ∀ {n₁ n₂: Nat}, n₁.double = n₂.double → n₁ = n₂
      | 0,      0,      _ => rfl
      | 0,      _  + 1, h => (nomatch h) |> absurd h |> False.elim
      | _  + 1,  0,     h => (nomatch h) |> absurd h |> False.elim
      | n₁ + 1, n₂ + 1, h =>
        have ih :=
          have: n₁.double = n₂.double := h |> Nat.succ_inj |> Nat.succ_inj
          _example this
        congrArg Nat.succ ih

    theorem Bool.beq_true: ∀ {n₁ n₂: Nat}, (n₁ == n₂) = true → n₁ = n₂
      | 0,      0,      _ => rfl
      | 0,      _  + 1, h => (nomatch h) |> absurd h |> False.elim
      | _  + 1, 0,      h => (nomatch h) |> absurd h |> False.elim
      | n₁ + 1, n₂ + 1, h =>
        have ih :=
          have: (n₁ == n₂) = true := sorry
          beq_true this
        congrArg Nat.succ ih

    example: ∀ {n₁ n₂: Nat}, n₁ + n₁ = n₂ + n₂ → n₁ = n₂
      | 0,      0,      _ => rfl
      | 0,      _  + 1, h => (nomatch h) |> absurd h |> False.elim
      | _  + 1, 0,      h => (nomatch h) |> absurd h |> False.elim
      | n₁ + 1, n₂ + 1, h =>
        have ih :=
          have: n₁ + n₁ = n₂ + n₂ :=
            have: (n₁ + n₁).succ.succ = (n₂ + n₂).succ.succ :=
              calc (n₁ + n₁).succ.succ
                _ = (n₁.succ + n₁).succ := congrArg Nat.succ (Eq.symm (Nat.succ_add n₁ n₁))
                _ = n₁.succ + n₁.succ   := Eq.symm (Nat.add_succ n₁.succ n₁)
                _ = n₂.succ + n₂.succ   := h
                _ = (n₂.succ + n₂).succ := Nat.add_succ n₂.succ n₂
                _ = (n₂ + n₂).succ.succ := congrArg Nat.succ (Nat.succ_add n₂ n₂)
            this |> Nat.succ_inj |> Nat.succ_inj
          _example this
        congrArg Nat.succ ih

    example: ∀ {n: Nat}, ∀ {l: Poly.List α}, l.length = n → l.nth n = .none
      | n,     .nil,        _ => rfl
      | 0,     .cons hd tl, h => sorry
      | n + 1, .cons hd tl, h =>
        have ih :=
          have: tl.length = n := sorry
          _example this
        sorry
  end Term

  namespace Tactic
    example: ∀ n₁ n₂: Nat, n₁.double = n₂.double → n₁ = n₂ := by
      intro n₁
      induction n₁ with
        | zero =>
          intro
            | .zero, _ => rfl
            | .succ _, _ => contradiction
        | succ n₁ ih =>
          intro
            | .zero, _ => contradiction
            | .succ n₂, h =>
              apply f_equal
              · apply ih
                · simp at h
                  apply h

    theorem Bool.beq_true {n₁ n₂: Nat} (h: (n₁ == n₂) = true): n₁ = n₂ := by
      revert n₂
      induction n₁ with
        | zero =>
          intro
            | .zero, _ => rfl
            | .succ _, _ => contradiction
        | succ n₁ ih =>
          intro
            | .zero, _ => contradiction
            | .succ n₂, h =>
              apply f_equal
              · simp at ih
                apply ih
                · simp at h
                  apply h

    example: ∀ n₁ n₂: Nat, n₁ + n₁ = n₂ + n₂ → n₁ = n₂ := by
      intro n₁
      induction n₁ with
        | zero =>
          intro
            | .zero, _ => rfl
            | .succ _, _ => contradiction
        | succ n₁ ih =>
          intro
            | .zero, _ => contradiction
            | .succ n₂, h => sorry

    example {n₁ n₂: Nat} (h: n₁.double = n₂.double): n₁ = n₂ := by
      revert n₁
      induction n₂ with
        | zero =>
          intro
            | .zero, _ => rfl
            | .succ _, _ => contradiction
        | succ n₂ ih =>
          intro
            | .zero, _ => contradiction
            | .succ n₂, h =>
              apply f_equal
              · apply ih
                · simp at h
                  apply h

    example {n: Nat} {l: Poly.List α} (h: l.length = n): l.nth n = .none := by
      revert n
      induction l with
        | nil =>
          intro
            | .zero, _ => rfl
            | .succ _, _ => contradiction
        | cons hd tl ih =>
          intro
            | .zero, _ => sorry --contradiction
            | .succ n, h => sorry
  end Tactic

  namespace Blended
    example: ∀ {n₁ n₂: Nat}, n₁.double = n₂.double → n₁ = n₂
      | 0,      0,      _ => by rfl
      | 0,      _  + 1, h => by contradiction
      | _  + 1, 0,      h => by contradiction
      | n₁ + 1, n₂ + 1, h => by
        have ih :=
          have: n₁.double = n₂.double := h |> Nat.succ_inj |> Nat.succ_inj
          _example this
        rw [ih]

    theorem Bool.beq_true: ∀ {n₁ n₂: Nat}, (n₁ == n₂) = true → n₁ = n₂
      | 0,      0,      _ => by rfl
      | 0,      _  + 1, h => by contradiction
      | _  + 1, 0,      h => by contradiction
      | n₁ + 1, n₂ + 1, h =>
        have ih :=
          have: (n₁ == n₂) = true := sorry
          beq_true this
        by rw [ih]

    example: ∀ {n₁ n₂: Nat}, n₁ + n₁ = n₂ + n₂ → n₁ = n₂
      | 0,      0,      _ => by rfl
      | 0,      _  + 1, h => by contradiction
      | _  + 1, 0,      h => by contradiction
      | n₁ + 1, n₂ + 1, h =>
        have ih :=
          have: n₁ + n₁ = n₂ + n₂ :=
            have: (n₁ + n₁).succ.succ = (n₂ + n₂).succ.succ :=
              calc (n₁ + n₁).succ.succ
                _ = n₁.succ + n₁.succ   := by simp [Nat.add_succ, Nat.succ_add]
                _ = n₂.succ + n₂.succ   := by rw [h]
                _ = (n₂ + n₂).succ.succ := by simp [Nat.add_succ, Nat.succ_add]
            this |> Nat.succ_inj |> Nat.succ_inj
          _example this
        by rw [ih]

    example: ∀ {n: Nat}, ∀ {l: Poly.List α}, l.length = n → l.nth n = .none
      | n,     .nil,        _ => by rfl
      | 0,     .cons hd tl, h => sorry -- by contradiction
      | n + 1, .cons hd tl, h =>
        have ih :=
          have: tl.length = n := sorry
          _example this
        sorry
  end Blended

  /-
  ## Unfolding Definitions

  Here, we use `unfold` when appropriate, but also Lean's `@[reducible]`
  annotation to mark definitions as automatically `unfold`-able by the `simp`
  tactic.
  -/

  @[reducible]
  def _root_.Nat.square (n: Nat): Nat := n * n

  @[reducible]
  private def _root_.Nat.foo (_: Nat): Nat := 5

  @[reducible]
  private def _root_.Nat.bar: Nat → Nat
    | 0     => 5
    | _ + 1 => 5

  namespace Term
    theorem Nat.square_mult (n₁ n₂: Nat): (n₁ * n₂).square = n₁.square * n₂.square :=
      have h: n₁ * n₂ * n₁ = n₁ * n₁ * n₂ :=
        calc n₁ * n₂ * n₁
          _ = n₁ * (n₁ * n₂) := Nat.mul_comm (n₁ * n₂) n₁
          _ = n₁ * n₁ * n₂   := Eq.symm (Nat.mul_assoc n₁ n₁ n₂)
      calc (n₁ * n₂).square
        _ = (n₁ * n₂) * (n₁ * n₂) := rfl
        _ = (n₁ * n₂ * n₁) * n₂   := Eq.symm (Nat.mul_assoc (n₁ * n₂) n₁ n₂)
        _ = (n₁ * n₁ * n₂) * n₂   := congrArg (· * n₂) h
        _ = (n₁ * n₁) * (n₂ * n₂) := Nat.mul_assoc (n₁ * n₁) n₂ n₂
        _ = n₁.square * n₂.square := rfl

    example {n: Nat}: n.foo + 1 = (n + 1).foo + 1 := rfl

    example: ∀ n: Nat, n.bar + 1 = (n + 1).bar + 1
      | 0 | _ + 1 => rfl
  end Term

  namespace Tactic
    theorem Nat.square_mult (n₁ n₂: Nat): (n₁ * n₂).square = n₁.square * n₂.square := by
      have h: n₁ * n₂ * n₁ = n₁ * n₁ * n₂ := by
        rw [Nat.mul_comm, Nat.mul_assoc]
      unfold Nat.square
      rw [← Nat.mul_assoc, h, Nat.mul_assoc]

    example {n: Nat}: n.foo + 1 = (n + 1).foo + 1 := by
      rfl

    example: ∀ n: Nat, n.bar + 1 = (n + 1).bar + 1 := by
      intro
        | .zero => rfl
        | .succ _ => rfl
  end Tactic

  namespace Blended
    theorem Nat.square_mult (n₁ n₂: Nat): (n₁ * n₂).square = n₁.square * n₂.square :=
      have h: n₁ * n₂ * n₁ = n₁ * n₁ * n₂ := by
        rw [Nat.mul_comm, Nat.mul_assoc]
      calc (n₁ * n₂).square
        _ = (n₁ * n₂ * n₁) * n₂   := by simp [Nat.mul_assoc]
        _ = (n₁ * n₁ * n₂) * n₂   := by rw [h]
        _ = n₁.square * n₂.square := by simp [Nat.mul_assoc]

    example {n: Nat}: n.foo + 1 = (n + 1).foo + 1 := rfl

    example: ∀ n: Nat, n.bar + 1 = (n + 1).bar + 1
      | 0 | _ + 1 => by rfl
  end Blended

  /-
  ## Using `cases` (Coq's `destruct`) on Compound Expressions
  -/

  @[reducible]
  private def _root_.Nat.silly (n: Nat): Bool :=
    if n == 3
    then false
    else if n == 5
         then false
         else false

  @[reducible]
  private def _root_.Nat.alsoSilly (n: Nat): Bool :=
    if n == 3
    then true
    else if n == 5
         then true
         else false

  namespace Term
    -- TODO: Remove Tactic Block
    example {n: Nat}: n.silly = false :=
      match h₁: n == 3 with
        | true =>
          calc n.silly
            _ = if n == 3 then false else if n == 5 then false else false := rfl
            _ = false                                                     := by simp [h₁]
        | false =>
          match h₂: n == 5 with
            | true =>
              calc n.silly
                _ = if n == 3 then false else if n == 5 then false else false := rfl
                _ = if n == 5 then false else false                           := by simp [h₁]
                _ = false                                                     := by simp [h₂]
            | false =>
              calc n.silly
                _ = if n == 3 then false else if n == 5 then false else false := rfl
                _ = if n == 5 then false else false                           := by simp [h₁]
                _ = false                                                     := by simp [h₂]

    open Poly
    theorem Poly.List.combine_split: ∀ l₁: Poly.List (α ‹×› β), ∀ l₂: Poly.List α, ∀ l₃: Poly.List β, l₁.split = (‹l₂, l₃›) → l₂.combine l₃ = l₁
      | [‹›], [‹›], [‹›], _ => rfl
      | (‹l, r›) ::: tl₁, hd₂ ::: tl₂, hd₃ ::: tl₃, h =>
        have ih :=
          have: tl₁.split = (‹tl₂, tl₃›) := sorry
          combine_split tl₁ tl₂ tl₃ this
        sorry

    -- TODO: Remove Tactic Block
    example {n: Nat} (h: n.alsoSilly = true): (n % 2 == 1) == true :=
      match h₁: n == 3 with
        | true =>
          have heq := Bool.beq_true h₁
          calc (n % 2 == 1) == true
            _ = ((3 % 2 == 1) == true) := congrArg (· == true) (congrArg (· % 2 == 1) heq)
            _ = true                   := rfl
        | false =>
          match h₂: n == 5 with
            | true =>
              have heq := Bool.beq_true h₂
              calc (n % 2 == 1) == true
                _ = ((5 % 2 == 1) == true) := congrArg (· == true) (congrArg (· % 2 == 1) heq)
                _ = true                   := rfl
            | false =>
              have h₃: true = false :=
                calc true
                  _ = n.alsoSilly := Eq.symm h
                  _ = if n == 3 then true else if n == 5 then true else false := rfl
                  _ = if n == 5 then true else false                          := by simp [h₁]
                  _ = false                                                   := by simp [h₂]
              (nomatch h₃) |> absurd h₃ |> False.elim

    example {f: Bool → Bool}: ∀ b: Bool, f (f (f b)) = f b
      | true =>
        match h₁: f true with
          | true =>
            calc f (f true)
              _ = f true := congrArg f h₁
              _ = true   := h₁
          | false =>
            match h₂: f false with
              | true => h₁
              | false => h₂
      | false =>
        match h₁: f false with
          | true =>
            match h₂: f true with
              | true => h₂
              | false => h₁
          | false =>
            calc f (f false)
              _ = f (false) := congrArg f h₁
              _ = false     := h₁
  end Term

  namespace Tactic
    example {n: Nat}: n.silly = false := by
      unfold Nat.silly
      cases n == 3 with
        | true => simp
        | false =>
          cases n == 5 with
            | true => simp
            | false => simp

    open Poly
    theorem Poly.List.combine_split: ∀ l₁: Poly.List (α ‹×› β), ∀ l₂: Poly.List α, ∀ l₃: Poly.List β, l₁.split = (‹l₂, l₃›) → l₂.combine l₃ = l₁ := by sorry

    example {n: Nat} (h: n.alsoSilly): n % 2 == 1 := by
      unfold Nat.alsoSilly at h
      cases h₁: n == 3 with
        | true => simp [Bool.beq_true h₁]
        | false =>
          cases h₂: n == 5 with
            | true => simp [Bool.beq_true h₂]
            | false => simp [h₁, h₂] at h

    example {f: Bool → Bool} {b: Bool}: f (f (f b)) = f b := by
      cases h₁: b with
        | true =>
          cases h₂: f true with
            | true => rw [h₂, h₂]
            | false =>
              cases h₃: f false with
                | true => apply h₂
                | false => apply h₃
        | false =>
          cases h₂: f false with
            | true =>
              cases h₃: f true with
                | true => apply h₃
                | false => apply h₂
            | false => rw [h₂, h₂]
  end Tactic

  namespace Blended
    example {n: Nat}: n.silly = false :=
      if h₁: n == 3
      then by unfold Nat.silly; simp [h₁]
      else if h₂: n == 5
           then by unfold Nat.silly; simp [h₁, h₂]
           else by unfold Nat.silly; simp [h₁, h₂]

    open Poly
    theorem Poly.List.combine_split: ∀ l₁: Poly.List (α ‹×› β), ∀ l₂: Poly.List α, ∀ l₃: Poly.List β, l₁.split = (‹l₂, l₃›) → l₂.combine l₃ = l₁
      | [‹›], [‹›], [‹›], _ => by rfl
      | (‹l, r›) ::: tl₁, hd₂ ::: tl₂, hd₃ ::: tl₃, h => by sorry

    example (n: Nat) (h: n.alsoSilly = true): (n % 2 == 1) == true :=
      if h₁: n == 3
      then by simp [Bool.beq_true h₁]
      else if h₂: n == 5
           then by simp [Bool.beq_true h₂]
           else by
             unfold Nat.alsoSilly at h
             simp [h₁, h₂] at h

    example {f: Bool → Bool}: ∀ b: Bool, f (f (f b)) = f b
      | true =>
        match h₁: f true with
          | true => by rw [h₁, h₁]
          | false =>
            match h₂: f false with
              | true => h₁
              | false => h₂
      | false =>
        match h₁: f false with
          | true =>
            match h₂: f true with
              | true => h₂
              | false => h₁
          | false => by rw [h₁, h₁]
  end Blended

  /-
  ## Review
  -/

  /-
  ## Additional Exercises
  -/

  def _root_.List.forall (p: α → Bool): List α → Bool
    | [] => true
    | hd :: tl =>
      if p hd
      then tl.forall p
      else false

  def _root_.List.exists (p: α → Bool): List α → Bool
    | [] => false
    | hd :: tl =>
      if p hd
      then true
      else tl.exists p

  def _root_.List.exists₂ (p: α → Bool) (l: List α): Bool :=
    l.forall (fun x => !(p x))

  section
    example: [1, 3, 5, 7, 9].forall (· % 2 == 1) = true := rfl
    example: [false, false].forall not = true := rfl
    example: [0, 2, 4, 5].forall (· % 2 == 0) = false := rfl
    example: [].forall (· == 5) = true := rfl

    example: [0, 2, 3, 6].exists (· == 5) = false := rfl
    example: [true, true, false].exists (true && ·) = true := rfl
    example: [1, 0, 0, 0, 0, 3].exists (· % 2 == 1) = true := rfl
    example: [].exists (· % 2 == 0) = false := rfl
  end

  namespace Term
    theorem Nat.beq_symm: ∀ {n₁ n₂: Nat}, n₁ == n₂ → n₂ == n₁
      | 0,      0,      _ => rfl
      | 0,      _  + 1, h => (nomatch h) |> absurd h |> False.elim
      | _  + 1, 0,      h => (nomatch h) |> absurd h |> False.elim
      | n₁ + 1, n₂ + 1, h =>
        have ih :=
          have: n₁ == n₂ := sorry
          beq_symm this
        sorry

    theorem Nat.beq_trans {n₁ n₂ n₃: Nat} (h₁: n₁ == n₂) (h₂: n₂ == n₃): n₁ == n₃ :=
      have h₁: n₁ = n₂ := sorry
      have h₂: n₂ = n₃ := sorry
      have h₃: n₁ = n₃ := trans h₁ h₂
      sorry

    open Poly
    theorem List.split_combine: ∀ l₁: Poly.List α, ∀ l₂: Poly.List β, ∀ l₃: Poly.List (α ‹×› β), l₁.combine l₂ = l₃ → l₃.split = (‹l₁, l₂›) := sorry

    example {p: α → Bool} {hd: α} {l tl: Poly.List α}: l.filter p = hd ::: tl → p hd = true := sorry

    theorem List.exists_eq_exists₂ {p: α → Bool}: ∀ l: _root_.List α, l.exists p = l.exists₂ p := sorry
  end Term

  namespace Tactic
    theorem Nat.beq_symm: ∀ {n₁ n₂: Nat}, n₁ == n₂ → n₂ == n₁ := by sorry

    theorem Nat.beq_trans {n₁ n₂ n₃: Nat} (h₁: n₁ == n₂) (h₂: n₂ == n₃): n₁ == n₃ := by
      rw [Nat.beq_eq_true_eq] at h₁
      rw [Nat.beq_eq_true_eq] at h₂
      rw [Nat.beq_eq_true_eq]
      apply trans h₁ h₂

    open Poly
    theorem List.split_combine: ∀ l₁: Poly.List α, ∀ l₂: Poly.List β, ∀ l₃: Poly.List (α ‹×› β), l₁.combine l₂ = l₃ → l₃.split = (‹l₁, l₂›) := by sorry

    example {p: α → Bool} {hd: α} {l tl: Poly.List α}: l.filter p = hd ::: tl → p hd = true := by sorry

    theorem List.exists_eq_exists₂ {p: α → Bool}: ∀ l: _root_.List α, l.exists p = l.exists₂ p := by sorry
  end Tactic

  namespace Blended
    theorem Nat.beq_symm: ∀ {n₁ n₂: Nat}, n₁ == n₂ → n₂ == n₁
      | 0,      0,      _ => by rfl
      | 0,      _  + 1, h => by contradiction
      | _  + 1, 0,      h => by contradiction
      | n₁ + 1, n₂ + 1, h =>
        have ih :=
          have: n₁ == n₂ := sorry
          beq_symm this
        sorry

    theorem Nat.beq_trans {n₁ n₂ n₃: Nat} (h₁: n₁ == n₂) (h₂: n₂ == n₃): n₁ == n₃ := sorry

    open Poly
    theorem List.split_combine: ∀ l₁: Poly.List α, ∀ l₂: Poly.List β, ∀ l₃: Poly.List (α ‹×› β), l₁.combine l₂ = l₃ → l₃.split = (‹l₁, l₂›) := by sorry

    example {p: α → Bool} {hd: α} {l tl: Poly.List α}: l.filter p = hd ::: tl → p hd = true := by sorry

    theorem List.exists_eq_exists₂ {p: α → Bool}: ∀ l: _root_.List α, l.exists p = l.exists₂ p := by sorry
  end Blended
end SoftwareFoundations.LogicalFoundations.Tactics
