/-
# Untyped Arithmetic
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-- Terms -/
inductive Term: Type where
  | true: Term
  | false: Term
  | zero: Term
  | pred: Term → Term
  | succ: Term → Term
  | isZero: Term → Term
  | ite: Term → Term → Term → Term
deriving DecidableEq

/-- Construct the set of constant terms within a term -/
@[simp]
def Term.consts: Term → Finset Term
  | .true =>   { .true }
  | .false => { .false }
  | .zero => { .zero }
  | .pred t | .succ t | .isZero t => t.consts
  | .ite c t f => c.consts ∪ t.consts ∪ f.consts

/-- Compute the number terms in a term -/
@[simp]
def Term.size: Term → Nat
  | .true | .false | .zero => 1
  | .pred t | .succ t | .isZero t => 1 + t.size
  | .ite c t f => 1 + c.size + t.size + f.size

/-- Compute the maximum depth of a term -/
@[local simp]
def Term.depth: Term → Nat
  | .true | .false | .zero => 1
  | .pred t | .succ t | .isZero t => 1 + t.depth
  | .ite c t f => 1 + Nat.max (Nat.max c.depth t.depth) f.depth

@[local simp]
def Term.isValue: Term → Bool
  | .true | .false => Bool.true
  | _ => Bool.false

@[local simp]
def Term.eval1: Term → Term
  | .true => true
  | .false => false
  | .zero => .zero
  | .pred t => t
  | .succ t => t
  | .isZero .zero => .true
  | .isZero t => isZero t.eval1
  | .ite .true t _ => t
  | .ite .false _ t => t
  | .ite c t f => .ite c.eval1 t f

-- @[local simp]
-- def Term.eval (t: Term): Term :=
--   let t₁: Term := t.eval1
--   if t₁.isValue then t₁ else t₁.eval
/-

theorem Term.constsLteSize:
  ∀ t: Term, t.consts.card <= t.size := by
    intro t
    induction t with
      | true => simp
      | false => simp
      | zero => simp
      | pred t₁ ht₁ =>
        rw [Term.consts, Term.size]
      | ite c t f ihc iht ihf =>
        rw [Term.consts, Term.size]
        rw [Finset.card_union_eq, Finset.card_union_eq]




      -- simp
      -- | ite c t f ihc iht ihf =>
      --   rw [Finset.card_union_eq, Finset.card_union_eq]
      --   sorry

theorem Term.eval1Deterministic:
  ∀ t t₁ t₂: Term,
  t.eval1 = t₁ → t.eval1 = t₂ → t₁ = t₂ := by
    intro t t₁ t₂
    induction t with
      | true => sorry
      | false => sorry
      | ite c t f ihc iht ihf => sorry

theorem Term.isNormalForm (t: Term):
  t.eval1 = t := by
    induction t with
      rw [Term.eval1]
      | ite c t f ihc iht ihf => sorry

theorem Term.valueIsInNormalForm:
  ∀ t: Term,
  t.isValue → t.isNormalForm := by sorry

theorem Term.normalFormsAreValues:
  ∀ t: Term,
  t.isNormalForm → t.isValue := by sorry

-/
