/-
# Typed Arithmetic
-/

import «Tapl».«Preliminaries»

namespace «Tapl».«TyArith»
  inductive Ty: Type where
    | bool: Ty
    | nat: Ty
  deriving Repr, DecidableEq

  inductive Term: Ty → Type where
    | true: Term .bool
    | false: Term .bool
    | zero: Term .nat
    | pred: Term .nat → Term .nat
    | succ: Term .nat → Term .nat
    | isZero: Term .nat → Term .bool
    | ite: Term .bool → Term α → Term α → Term α
  deriving Repr, DecidableEq

  def Term.typeOf: Term α → Ty
    | .true => .bool
    | .false => .bool
    | .zero => .nat
    | .pred n =>
      match n.typeOf with
        | .nat => .nat
        | _ => sorry
    | .succ n =>
      match n.typeOf with
        | .nat => .nat
        | _ => sorry
    | .isZero n =>
      match n.typeOf with
        | .nat => .nat
        | _ => sorry
    | .ite c t f =>
      let tyt := t.typeOf
      let tyf := f.typeOf
      match c.typeOf with
        | .bool =>
          if tyt == tyf
          then tyt
          else sorry
        | _ => sorry

  def Term.eval₁: Term α → Term α
    | .true => .true
    | .false => .false
    | .zero => .zero
    | .pred .zero => .zero
    | .pred (.succ n) => n
    | .pred n => n.eval₁.pred
    | .succ .zero => Term.zero.succ
    | .succ n => n.eval₁.succ
    | .isZero .zero => .true
    | .isZero (.succ _) => .false
    | .isZero n => n.eval₁.isZero
    | .ite .true t _ => t
    | .ite .false _ f => f
    | .ite c t f => .ite c.eval₁ t f

  def Term.eval: Term α → Term α
    | .true => .true
    | .false => .false
    | .zero => .zero
    | .pred n =>
      match n.eval with
        | .zero => .zero
        | .succ n => n
        | _ => sorry
    | .succ n => n.eval.succ
    | .isZero n =>
      match n.eval with
        | .zero => .true
        | _ => .false
    | .ite c t f =>
      match c.eval with
        | .true => t.eval
        | .false => f.eval
        | _ => sorry

  inductive TypeOf: Term α → Ty → Prop where
    | true: TypeOf Term.true .bool
    | false: TypeOf Term.false .bool
    | zero: TypeOf Term.zero .nat
    | pred (n: Term .nat): TypeOf n.pred .nat
    | succ (n: Term .nat): TypeOf n.succ .nat
    | isZero (n: Term .nat): TypeOf n.isZero .nat
    | ite (c: Term .bool) {t f: Term α}: TypeOf (.ite c t f) α

  inductive Numeric: Term .nat → Prop where
    | zero: Numeric .zero
    | succ (t: Term .nat) (h: Numeric t): Numeric t.succ

  inductive Value: Term α → Prop where
    | numeric (t: Term .nat) (h: Numeric t): Value t
    | true: Value .true
    | false: Value .false

  inductive Eval₁: Term α → Term α → Prop where
    | iteTrue (α: Ty) (t f: Term α): Eval₁ (.ite .true t f) t
    | iteFalse (α: Ty) (t f: Term α): Eval₁ (.ite .false t f) f
    | ite (α: Ty) (c₁ c₂: Term .bool) (t f: Term α) (h: Eval₁ c₁ c₂): Eval₁ (.ite c₁ t f) (.ite c₂ t f)
    | succ (t₁ t₂: Term .nat) (h: Eval₁ t₁ t₂): Eval₁ t₁.succ t₂.succ
    | predZero: Eval₁ Term.zero.pred .zero
    | predSucc (t: Term .nat) (h: Numeric t): Eval₁ t.succ.pred t
    | pred (t₁ t₂: Term .nat) (h: Eval₁ t₁ t₂): Eval₁ t₁.pred t₂.pred
    | isZeroZero: Eval₁ Term.zero.isZero .true
    | isZeroSucc (t: Term .nat) (h: Numeric t): Eval₁ t.succ.isZero .false
    | isZero (t₁ t₂: Term .nat) (h: Eval₁ t₁ t₂): Eval₁ t₁isZero t₂.isZero

  inductive Eval: Term α → Term α → Prop where
    | iteTrue (α: Ty) (c: Term .bool) (t₁ t₂ f: Term α) (h₁: Eval c Term.true) (h₂: Value t₁) (h₃: Eval t₁ t₂): Eval (.ite c t₁ f) t₂
    | iteFalse (α: Ty) (c: Term .bool) (t f₁ f₂: Term α) (h₁: Eval c Term.false) (h₂: Value f₂) (h₃: Eval f₁ f₂): Eval (.ite c t f₁) f₂
    | succ (t₁ t₂: Term .nat) (h₁: Numeric t₂) (h₂: Eval t₁ t₂): Eval t₁.succ t₂.succ
    | predZero (t: Term .nat) (h: Eval t Term.zero): Eval t.pred Term.zero
    | predSucc (t₁ t₂: Term .nat) (h₁: Numeric t₂) (h₂: Eval t₁ t₂.succ): Eval t₁.pred t₂
    | isZeroZero (t₁: Term .nat) (h: Eval t₁ .zero): Eval t₁.isZero .true
    | isZeroSucc (t₁ t₂: Term .nat) (h₁: Numeric t₂) (h₂: Eval t₁ t₂.succ): Eval t₁.isZero .false

  section Examples
    def true: Term .bool := Term.true
    def false: Term .bool := Term.false
    def zero: Term .nat := Term.zero
    def one: Term .nat := zero.succ
    def two: Term .nat := one.succ

    section eval₁
      example: true.eval₁ = true := rfl
      example: false.eval₁ = false := rfl
      example: zero.eval₁ = zero := rfl
      example: zero.pred.eval₁ = zero := rfl
      example: two.pred.eval₁ = one := rfl
      example: two.pred.pred.eval₁ = one.pred := rfl
      example: one.eval₁ = one := rfl
      example: two.eval₁ = two := rfl
      example: one.pred.succ.eval₁ = one := rfl
      example: zero.isZero.eval₁ = true := rfl
      example: one.isZero.eval₁ = false := rfl
      example: two.isZero.eval₁ = false := rfl
      example: one.pred.succ.pred.isZero.eval₁ = one.pred.isZero := rfl
      example: zero.pred.isZero.eval₁ = zero.isZero := rfl
      example: zero.pred.pred.isZero.eval₁ = zero.pred.isZero := rfl
      example: (Term.ite true one zero).eval₁ = one := rfl
      example: (Term.ite false one zero).eval₁ = zero := rfl
      example: (Term.ite zero.isZero one zero).eval₁ = Term.ite true one zero := rfl
    end eval₁

    section Numeric
      theorem one_numeric: Numeric one := Numeric.succ Numeric.zero
    end Numeric

    section Eval₁
      private theorem zero_pred_one: Eval₁ one.pred zero := .predSucc .zero
      private theorem one_pred_two: Eval₁ two.pred one := .predSucc one_numeric

      example: Eval₁ true true := sorry
      example: Eval₁ false false := sorry
      example: Eval₁ zero zero := sorry
      example: Eval₁ zero.pred zero := .predZero
      example: Eval₁ two.pred.pred one.pred := .pred one_pred_two
      example: Eval₁ one one := sorry
      example: Eval₁ two two := sorry
      example: Eval₁ one.pred.succ one := .succ zero_pred_one
      example: Eval₁ zero.isZero .true := .isZeroZero
      example: Eval₁ one.isZero .false := .isZeroSucc Numeric.zero
      example: Eval₁ two.isZero .false := .isZeroSucc one_numeric
      example: Eval₁ one.pred.succ.pred.isZero one.pred.isZero :=
        have predSuccNumeric: Numeric one.pred :=
          have zeroNumeric: Numeric zero := .zero
          sorry
        .isZero (.predSucc predSuccNumeric)
      example: Eval₁ zero.pred.isZero zero.isZero := .isZero .predZero
      example: Eval₁ zero.pred.pred.isZero zero.pred.isZero := .isZero (.pred .predZero)
      example: Eval₁ (.ite true one zero) one := .iteTrue
      example: Eval₁ (.ite false one zero) zero := .iteFalse
      example: Eval₁ (.ite zero.isZero one zero) (.ite true one zero) := .ite .isZeroZero
    end Eval₁

    section eval
      example: true.eval = true := rfl
      example: false.eval = false := rfl
      example: zero.eval = zero := rfl
      example: zero.pred.eval = zero := rfl
      example: two.pred.eval = one := rfl
      example: two.pred.pred.eval = zero := rfl
      example: one.eval = one := rfl
      example: two.eval = two := rfl
      example: one.pred.succ.eval = one := rfl
      example: zero.isZero.eval = true := rfl
      example: one.isZero.eval = false := rfl
      example: two.isZero.eval = false := rfl
      example: one.pred.succ.pred.isZero.eval = true := rfl
      example: zero.pred.isZero.eval = true := rfl
      example: zero.pred.pred.isZero.eval = true := rfl
      example: (Term.ite true one zero).eval = one := rfl
      example: (Term.ite false one zero).eval = zero := rfl
      example: (Term.ite zero.isZero one zero).eval = one := rfl
    end eval

    section Eval
      example: Eval true true := sorry
      example: Eval false false := sorry
      example: Eval zero zero := sorry
      example: Eval zero.pred zero := sorry -- rfl
      example: Eval two.pred one := sorry -- rfl
      example: Eval two.pred.pred zero := sorry -- rfl
      example: Eval one one := sorry
      example: Eval two two := sorry
      example: Eval one.pred.succ one := sorry -- rfl
      example: Eval zero.isZero true := sorry -- rfl
      example: Eval one.isZero false := sorry -- rfl
      example: Eval two.isZero false := sorry -- rfl
      example: Eval one.pred.succ.pred.isZero true := sorry -- rfl
      example: Eval zero.pred.isZero true := sorry -- rfl
      example: Eval zero.pred.pred.isZero true := sorry -- rfl
      example: Eval (Term.ite true one zero) one := sorry -- rfl
      example: Eval (Term.ite false one zero) zero := sorry -- rfl
      example: Eval (Term.ite zero.isZero one zero) one := sorry -- rfl
    end Eval
  end Examples

  theorem typeOf_typeOf {α: Ty} {t: Term α}: TypeOf t α ↔ t.typeOf = α := sorry

  theorem eval₁_eval₁ {α: Ty} {t₁ t₂: Term α}: Eval₁ t₁ t₂ ↔ t₁.eval₁ = t₂ := sorry

  theorem eval_eval {α: Ty} {t₁ t₂: Term α}: Eval t₁ t₂ ↔ t₁.eval = t₂.eval := sorry

  theorem eval_rtc_eval₁ {α: Ty} {t₁ t₂: Term α}: RTC Eval₁ t₁ t₂ ↔ Eval t₁ t₂ := sorry

  theorem ty_uniq {α β: Ty} {t: Term α} (h₁: TypeOf t α) (h₂: TypeOf t β): α = β := by
    cases h₁ <;> cases h₂ <;> rfl

  theorem ty_deriv_uniq: True := sorry

  theorem canonical_forms₁: ∀ t: Term .bool, Value t → t = Term.true ∨ t = Term.false
    | .true, .true => .inl rfl
    | .false, .false => .inr rfl

  theorem canonical_forms₂: ∀ t: Term .nat, Value t → Numeric t
    | .zero, .numeric nv => nv
    | .succ _, .numeric nv => nv

  theorem TypeOf.progress {α: Ty}: ∀ t₁: Term α, TypeOf t₁ α → Value t₁ ∨ ∃ t₂: Term α, Eval₁ t₁ t₂ := sorry
  theorem TypeOf.preservation {α: Ty} {t₁ t₂: Term α}: Eval₁ t₁ t₂ → TypeOf t₂ α := sorry
end «Tapl».«TyArith»
