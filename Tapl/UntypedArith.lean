/-
# Untyped Arithmetic
-/

import «Tapl».«Preliminaries»

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace Tapl.UntypedArith
  inductive Term: Type where
    | true: Term
    | false: Term
    | zero: Term
    | pred: Term → Term
    | succ: Term → Term
    | isZero: Term → Term
    | ite: Term → Term → Term → Term
  deriving Repr, DecidableEq

  def Term.consts: Term → Finset Term
    | .true =>   { .true }
    | .false => { .false }
    | .zero => { .zero }
    | .pred t | .succ t | .isZero t => t.consts
    | .ite c t f => c.consts ∪ t.consts ∪ f.consts

  def Term.size: Term → Nat
    | .true | .false | .zero => 1
    | .pred t | .succ t | .isZero t => 1 + t.size
    | .ite c t f => 1 + c.size + t.size + f.size

  @[local simp]
  def Term.depth: Term → Nat
    | .true | .false | .zero => 1
    | .pred t | .succ t | .isZero t => 1 + t.depth
    | .ite c t f => 1 + Nat.max (Nat.max c.depth t.depth) f.depth

  def Term.isNumeric: Term → Bool
    | .zero => Bool.true
    | .succ n => n.isNumeric
    | _ => Bool.false

  def Term.isValue: Term → Bool
    | .true | .false => Bool.true
    | t => t.isNumeric

  def Term.eval₁: Term → Term
    | .true => .true
    | .false => .false
    | .zero => .zero
    | .pred .zero => .zero
    | .pred t => t.eval₁.pred
    | .succ .zero => Term.zero.succ
    | .succ t => t.eval₁.succ
    | .isZero .zero => .true
    | .isZero (.succ _) => .false
    | .isZero t => t.eval₁.isZero
    | .ite .true t _ => t
    | .ite .false _ f => f
    | .ite c t f => .ite c.eval₁ t f

  def Term.eval: Term → Term
    | .true => .true
    | .false => false
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
        | .succ _ => .false
        | _ => sorry
    | .ite c t f =>
      match c.eval with
        | .true => t.eval
        | .false => f.eval
        | _ => sorry

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

  def Term.isNormal: ∀ t₁: Term, ¬ ∃ t₂: Term, Eval t₁ t₂ := sorry

  theorem eval₁_eval₁ (t₁ t₂: Term): Eval₁ t₁ t₂ ↔ t₁.eval₁ = t₂ := sorry

  theorem Eval₁.deterministic (t₁ t₂ t₃: Term): Eval₁ t₁ t₂ → Eval₁ t₁ t₃ → t₂ = t₃
    | .iteTrue t f, h => sorry
    | .iteFalse t f, h => sorry
    | .ite c₁ c₂ t f hc, h => sorry
    | .succ t₁ t₂ t, h => sorry
    | .predZero, h => sorry
    | .predSucc t hn, h => sorry
    | .pred t₁ t₂ ht, h => sorry
    | .isZeroZero, h => sorry
    | .isZeroSucc t ht, h => sorry
    | .isZero t₁ t₂ ht, h => sorry

  example (t₁ t₂ t₃: Term): Eval₁ t₁ t₂ → Eval₁ t₁ t₃ → t₂ = t₃ := by
    intro h₁₂ h₁₃
    induction h₁₂ with
      | iteTrue t f => sorry
      | iteFalse t f => sorry
      | ite c₁ c₂ t f hc ih => sorry
      | succ t₁ t₂ t ih => sorry
      | predZero => sorry
      | predSucc t hn => sorry
      | pred t₁ t₂ ht ih => sorry
      | isZeroZero => sorry
      | isZeroSucc t ht => sorry
      | isZero t₁ t₂ ht ih => sorry

  -- theorem Value.normal: ∀ t: Term, Value t → t.isNormal := sorry

  theorem eval_eval (t₁ t₂: Term): Eval t₁ t₂ ↔ t₁.eval = t₂ := sorry

  theorem eval_rtc_eval₁ (t₁ t₂: Term): RTC Eval₁ t₂ t₂ ↔ Eval t₁ t₂ := sorry

  -- theorem normal_unique (t₁ t₂ t₃: Term): t₂.isNormal → t₂.isNormal → Eval t₁ t₂ → Eval t₂ t₃ → t₂ = t₃ := sorry

  -- theorem Eval.termination (t₁: Term): ∃ t₂: Term, t₂.isNormal ∧ Eval t₁ t₂ := sorry
end Tapl.UntypedArith
