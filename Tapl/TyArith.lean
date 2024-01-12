/-
# Typed Arithmetic
-/

import «Tapl».«Preliminaries»

namespace Tapl.TyArith
  inductive Ty: Type where
    | bool: Ty
    | nat: Ty
  deriving Repr, DecidableEq

  inductive Term: Type where
    | true: Term
    | false: Term
    | zero: Term
    | pred: Term → Term
    | succ: Term → Term
    | isZero: Term → Term
    | ite: Term → Term → Term → Term
  deriving Repr, DecidableEq

  def Term.typeOf: Term → Ty
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

  def Term.eval₁: Term → Term
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

  def Term.eval: Term → Term
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

  inductive TypeOf: Term → Ty → Prop where
    | true: TypeOf Term.true Ty.bool
    | false: TypeOf Term.false Ty.bool
    | zero: TypeOf Term.zero Ty.nat
    | pred (n: Term): TypeOf n Ty.nat → TypeOf n.pred Ty.nat
    | succ (n: Term): TypeOf n Ty.nat → TypeOf n.succ Ty.nat
    | isZero (n: Term): TypeOf n Ty.nat → TypeOf n.isZero Ty.nat
    | ite (c t f: Term) (α: Ty): TypeOf c Ty.bool → TypeOf t α → TypeOf f α → TypeOf (.ite c t f) α

  inductive Numeric: Term → Prop where
    | zero: Numeric Term.zero
    | succ: ∀ nv: Term, Numeric nv → Numeric nv.succ

  inductive Value: Term → Prop where
    | numeric: ∀ nv: Term, Numeric nv → Value nv
    | true: Value Term.true
    | false: Value Term.false

  inductive Eval₁: Term → Term → Prop where
    | iteTrue: ∀ t f: Term, Eval₁ (.ite .true t f) t
    | iteFalse: ∀ t f: Term, Eval₁ (.ite .false t f) f
    | ite: ∀ c₁ c₂ t f: Term, Eval₁ c₁ c₂ → Eval₁ (.ite c₁ t f) (.ite c₂ t f)
    | succ: ∀ t₁ t₂: Term, Eval₁ t₁ t₂ → Eval₁ t₁.succ t₂.succ
    | predZero: Eval₁ Term.zero.pred .zero
    | predSucc: ∀ t: Term, Numeric t → Eval₁ t.succ.pred t
    | pred: ∀ t₁ t₂: Term, Eval₁ t₁ t₂ → Eval₁ t₁.pred t₂.pred
    | isZeroZero: Eval₁ Term.zero.isZero .true
    | isZeroSucc: ∀ t: Term, Numeric t → Eval₁ t.succ.isZero .false
    | isZero: ∀ t₁ t₂: Term, Eval₁ t₁ t₂ → Eval₁ t₁isZero t₂.isZero

  inductive Eval: Term → Term → Prop where
    | iteTrue: ∀ c t₁ t₂ f: Term, Eval c Term.true → Value t₁ → Eval t₁ t₂ → Eval (.ite c t₁ f) t₂
    | iteFalse: ∀ c t f₁ f₂: Term, Eval c Term.false → Value f₂ → Eval f₁ f₂ → Eval (.ite c t f₁) f₂
    | succ: ∀ t₁ t₂: Term, Numeric t₂ → Eval t₁ t₂ → Eval t₁.succ t₂.succ
    | predZero: ∀ t: Term, Eval t Term.zero → Eval t.pred Term.zero
    | predSucc: ∀ t₁ t₂: Term, Numeric t₂ → Eval t₁ t₂.succ → Eval t₁.pred t₂
    | isZeroZero: ∀ t₁: Term, Eval t₁ .zero → Eval t₁.isZero .true
    | isZeroSucc: ∀ t₁ t₂: Term, Numeric t₂ → Eval t₁ t₂.succ → Eval t₁.isZero .false

  theorem typeOf_typeOf: ∀ t: Term, ∀ ty: Ty, TypeOf t ty ↔ t.typeOf = ty := sorry

  theorem eval₁_eval₁: ∀ t₁ t₂: Term, Eval₁ t₁ t₂ ↔ t₁.eval₁ = t₂ := sorry

  theorem eval_eval: ∀ t₁ t₂: Term, Eval t₁ t₂ ↔ t₁.eval = t₂.eval := sorry

  theorem eval_rtc_eval₁: ∀ t₁ t₂: Term, RTC Eval₁ t₁ t₂ ↔ Eval t₁ t₂ := sorry

  theorem ty_uniq /-(t: Term) (ty₁ ty₂: Ty)-/ (h₁: TypeOf t ty₁) (h₂: TypeOf t ty₂): ty₁ = ty₂ := by
    cases h₁ with
      | true => cases h₂ <;> rfl
      | false => cases h₂ <;> rfl
      | zero => cases h₂ <;> rfl
      | pred n h => cases h₂ <;> rfl
      | succ n h => cases h₂ <;> rfl
      | isZero n h => cases h₂ <;> rfl
      | ite c t f ty h₁ h₂ h₃ =>
        cases h₂ with
          | ite c₁ t₂ f₁ ty₁ h₄ h₅ h₆ => sorry
          | _ => sorry

  theorem ty_deriv_uniq: True := sorry

  theorem canonical_forms₁: ∀ t: Term, Value t → TypeOf t Ty.bool → v = Term.true ∨ v = Term.false := sorry
  theorem canonical_forms₂: ∀ t: Term, Value t → TypeOf t Ty.nat → Numeric v := sorry

  theorem TypeOf.progress: ∀ t₁: Term, ∀ ty: Ty, TypeOf t₁ ty → Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
  theorem TypeOf.preservation: ∀ t₁ t₂: Term, ∀ ty: Ty, TypeOf t₁ ty → Eval₁ t₁ t₂ → TypeOf t₂ ty := sorry
end Tapl.TyArith
