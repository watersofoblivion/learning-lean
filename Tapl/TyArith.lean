/-
# Typed Arithmetic
-/

import «Tapl».«Preliminaries»

namespace Tapl.TyArith
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
    | isZero (n: Term .nat): TypeOf n .nat → TypeOf n.isZero .nat
    | ite (c: Term .bool) (t f: Term α): TypeOf (.ite c t f) α

  inductive Numeric: Term .nat → Prop where
    | zero: Numeric .zero
    | succ: Numeric nv → Numeric nv.succ

  inductive Value: Term α → Prop where
    | numeric: Numeric nv → Value nv
    | true: Value .true
    | false: Value .false

  inductive Eval₁: Term α → Term α → Prop where
    | iteTrue: ∀ t f: Term α, Eval₁ (.ite .true t f) t
    | iteFalse: ∀ t f: Term α, Eval₁ (.ite .false t f) f
    | ite: ∀ c₁ c₂: Term .bool, ∀ t f: Term α, Eval₁ c₁ c₂ → Eval₁ (.ite c₁ t f) (.ite c₂ t f)
    | succ: ∀ t₁ t₂: Term .nat, Eval₁ t₁ t₂ → Eval₁ t₁.succ t₂.succ
    | predZero: Eval₁ Term.zero.pred .zero
    | predSucc: ∀ t: Term .nat, Numeric t → Eval₁ t.succ.pred t
    | pred: ∀ t₁ t₂: Term .nat, Eval₁ t₁ t₂ → Eval₁ t₁.pred t₂.pred
    | isZeroZero: Eval₁ Term.zero.isZero .true
    | isZeroSucc: ∀ t: Term .nat, Numeric t → Eval₁ t.succ.isZero .false
    | isZero: ∀ t₁ t₂: Term .nat, Eval₁ t₁ t₂ → Eval₁ t₁isZero t₂.isZero

  inductive Eval: Term α → Term α → Prop where
    | iteTrue: ∀ c: Term .bool, ∀ t₁ t₂ f: Term α, Eval c Term.true → Value t₁ → Eval t₁ t₂ → Eval (.ite c t₁ f) t₂
    | iteFalse: ∀ c: Term .bool, ∀ t f₁ f₂: Term α, Eval c Term.false → Value f₂ → Eval f₁ f₂ → Eval (.ite c t f₁) f₂
    | succ: ∀ t₁ t₂: Term .nat, Numeric t₂ → Eval t₁ t₂ → Eval t₁.succ t₂.succ
    | predZero: ∀ t: Term .nat, Eval t Term.zero → Eval t.pred Term.zero
    | predSucc: ∀ t₁ t₂: Term .nat, Numeric t₂ → Eval t₁ t₂.succ → Eval t₁.pred t₂
    | isZeroZero: ∀ t₁: Term .nat, Eval t₁ .zero → Eval t₁.isZero .true
    | isZeroSucc: ∀ t₁ t₂: Term .nat, Numeric t₂ → Eval t₁ t₂.succ → Eval t₁.isZero .false

  theorem typeOf_typeOf: ∀ t: Term α, TypeOf t α ↔ t.typeOf = α := sorry

  theorem eval₁_eval₁: ∀ t₁ t₂: Term α, Eval₁ t₁ t₂ ↔ t₁.eval₁ = t₂ := sorry

  theorem eval_eval: ∀ t₁ t₂: Term α, Eval t₁ t₂ ↔ t₁.eval = t₂.eval := sorry

  theorem eval_rtc_eval₁: ∀ t₁ t₂: Term α , RTC Eval₁ t₁ t₂ ↔ Eval t₁ t₂ := sorry

  theorem ty_uniq (h₁: TypeOf t α) (h₂: TypeOf t β): α = β := by
    cases h₁ <;> cases h₂ <;> rfl

  theorem ty_deriv_uniq: True := sorry

  theorem canonical_forms₁: ∀ t: Term .bool, Value t → t = Term.true ∨ t = Term.false
    | .true, .true => .inl (rfl)
    | .false, .false => .inr (rfl)

  theorem canonical_forms₂: ∀ t: Term .nat, Value t → Numeric t
    | .zero, .numeric nv => nv
    | .succ _, .numeric nv => nv

  theorem TypeOf.progress: ∀ t₁: Term α, TypeOf t₁ α → Value t₁ ∨ ∃ t₂: Term α, Eval₁ t₁ t₂ := sorry
  theorem TypeOf.preservation: ∀ t₁ t₂: Term α, Eval₁ t₁ t₂ → TypeOf t₂ α := sorry
end Tapl.TyArith
