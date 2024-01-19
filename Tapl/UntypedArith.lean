/-
# Untyped Arithmetic
-/

import «Tapl».«Preliminaries»

import Mathlib.Init.Set
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

namespace «Tapl».«UntypedArith»
  /- 3.2.2 -/
  inductive Term: Type where
    | true: Term
    | false: Term
    -- | zero: Term
    -- | pred: Term → Term
    -- | succ: Term → Term
    -- | isZero: Term → Term
    | ite (c t f: Term): Term
  deriving Repr, DecidableEq

  -- TODO: Fix
  /- 3.2.3 -/
  def Term.termsᵢ: Nat → Finset Term
    | .zero => { Term.true, Term.false /-, Term.zero -/ }
    | .succ n =>
      let sn := Term.termsᵢ n
      let ite: Finset Term := { .ite Term.true Term.true Term.true }
      sn ∪ ite

  /- 3.2.3 -/
  def Term.terms: Set Term := ⋃ i, Term.termsᵢ i

  -- TODO: Fix
  /- Exersise 3.2.4 -/
  example: (Term.termsᵢ 3).card = 3 := rfl

  /- Exercise 3.2.5 -/
  theorem Term.termsᵢ.cumulative (i: Nat): Term.termsᵢ i ⊆ Term.termsᵢ i.succ := by
    induction i with
      | zero =>
        unfold Term.termsᵢ
        simp
      | succ n ih =>
        unfold Term.termsᵢ
        simp
        intro t h
        sorry

  /- 3.2.6 -/
  -- TODO

  /- 3.3.1 -/
  def Term.consts: Term → Finset Term
    | .true =>   { .true }
    | .false => { .false }
    -- | .zero => { .zero }
    -- | .pred t | .succ t | .isZero t => t.consts
    | .ite c t f => c.consts ∪ t.consts ∪ f.consts

  /- 3.3.2 -/
  def Term.size: Term → Nat
    | .true | .false => 1 --| .zero => 1
    -- | .pred t | .succ t | .isZero t => 1 + t.size
    | .ite c t f => 1 + c.size + t.size + f.size

  /- 3.3.2 -/
  def Term.depth: Term → Nat
    | .true | .false => 1 --| .zero => 1
    -- | .pred t | .succ t | .isZero t => 1 + t.depth
    | .ite c t f => 1 + (c.depth.max t.depth).max f.depth

  /- 3.3.3 -/
  example (t: Term): t.consts.card ≤ t.size := by
    induction t with
      | true => rfl
      | false => rfl
      | ite c t f ihc iht ihf =>
        -- calc (c.consts ∪ t.consts ∪ f.consts).card
        --   _ ≤ (c.consts ∪ t.consts).card + f.consts.card    := Finset.card_union_le (c.consts ∪ t.consts) f.consts
        --   _ = f.consts.card + (c.consts ∪ t.consts).card    := by rw [Nat.add_comm]
        --   _ ≤ f.consts.card + c.consts.card + t.consts.card := congrArg (Nat.add f.consts.card) (Finset.card_union_le c.consts t.consts)
        -- have h: c.consts.card + t.consts.card + f.consts.card ≤ c.size + t.size + f.size := sorry
        -- unfold Term.consts Term.size
        --
        -- rw [Finset.card_union_eq sorry, Finset.card_union_eq sorry]
        sorry

  def Term.isNumeric: Term → Bool
    -- | .zero => Bool.true
    -- | .succ n => n.isNumeric
    | _ => Bool.false

  def Term.isValue: Term → Bool
    | .true | .false => Bool.true
    | t => t.isNumeric

  def Term.eval₁: Term → Term
    | .true => .true
    | .false => .false
    -- | .zero => .zero
    -- | .pred .zero => .zero
    -- | .pred (.succ t) => t
    -- | .pred t => t.eval₁.pred
    -- | .succ .zero => Term.zero.succ
    -- | .succ t => t.eval₁.succ
    -- | .isZero .zero => .true
    -- | .isZero (.succ _) => .false
    -- | .isZero t => t.eval₁.isZero
    | .ite .true t _ => t
    | .ite .false _ f => f
    | .ite c t f => .ite c.eval₁ t f

  def Term.eval: Term → Term
    | .true => .true
    | .false => false
    -- | .zero => .zero
    -- | .pred n =>
    --   match n.eval with
    --     | .zero => .zero
    --     | .succ n => n
    --     | _ => sorry
    -- | .succ n => n.eval.succ
    -- | .isZero n =>
    --   match n.eval with
    --     | .zero => .true
    --     | .succ _ => .false
    --     | _ => sorry
    | .ite c t f =>
      match c.eval with
        | .true => t.eval
        | .false => f.eval
        | _ => sorry

  inductive Numeric: Term → Prop where
    -- | zero: Numeric Term.zero
    -- | succ {t: Term} (h: Numeric t): Numeric t.succ

  inductive Value: Term → Prop where
    -- | numeric {t: Term} (h: Numeric t): Value t
    | true: Value Term.true
    | false: Value Term.false

  /- 3.5.3 -/
  inductive Eval₁: Term → Term → Prop where
    | iteTrue (t f: Term): Eval₁ (.ite .true t f) t
    | iteFalse (t f: Term): Eval₁ (.ite .false t f) f
    | ite (c₁ c₂ t f: Term) (h: Eval₁ c₁ c₂): Eval₁ (.ite c₁ t f) (.ite c₂ t f)
    -- | succ (t₁ t₂: Term) (h: Eval₁ t₁ t₂): Eval₁ t₁.succ t₂.succ
    -- | predZero: Eval₁ Term.zero.pred .zero
    -- | predSucc (t: Term) (h: Numeric t): Eval₁ t.succ.pred t
    -- | pred (t₁ t₂: Term) (h: Eval₁ t₁ t₂): Eval₁ t₁.pred t₂.pred
    -- | isZeroZero: Eval₁ Term.zero.isZero .true
    -- | isZeroSucc (t: Term) (h: Numeric t): Eval₁ t.succ.isZero .false
    -- | isZero (t₁ t₂: Term) (h: Eval₁ t₁ t₂): Eval₁ t₁isZero t₂.isZero

  section
    /- 3.5.1 -/
    example: Eval₁ (.ite .true .true (.ite .false .false .false)) .true :=
      Eval₁.iteTrue .true (.ite .false .false .false)

    /- 3.5.3 -/
    private def s: Term := .ite .true .false .false
    private def t: Term := .ite s .true .true
    private def u: Term := .ite .false .true .true

    example: Eval₁ (.ite t .false .false) (.ite u .false .false) :=
      .iteTrue .false .false
        |> .ite s .false .true .true
        |> .ite t u .false .false

    example: Eval₁ (.ite t .false .false) (.ite u .false .false) := by
      apply Eval₁.ite
      · apply Eval₁.ite
        · apply Eval₁.iteTrue
  end

  /- 3.5.4 -/
  theorem Eval₁.deterministic {t₁ t₂ t₃: Term}: Eval₁ t₁ t₂ → Eval₁ t₁ t₃ → t₂ = t₃
    | .iteTrue .true _, .iteTrue .true _
    | .iteTrue .false _, .iteTrue .false _
    | .iteTrue (.ite _ _ _) _, .iteTrue (.ite _ _ _) _
    | .iteFalse _ .true, .iteFalse _ .true
    | .iteFalse _ .false, .iteFalse _ .false
    | .iteFalse _ (.ite _ _ _), .iteFalse _ (.ite _ _ _) => rfl
    | .ite _ c₁ _ _ hc₁, .ite _ c₂ _ _ hc₂ =>
      have h: c₁ = c₂ := Eval₁.deterministic hc₁ hc₂
      by rw [h]

    -- | .succ t₁, .succ t₂ => sorry
    -- | .succ t₁, h => sorry
    -- | .predZero, .predZero => rfl
    -- | .predZero, h => sorry
    -- | .predSucc hn₁, .predSucc hn₂ => sorry
    -- | .predSucc hn₁, h => sorry
    -- | .pred ht₁, .pred ht₂ => sorry
    -- | .pred ht₁, h => sorry
    -- | .isZeroZero, .isZeroZero => rfl
    -- | .isZeroZero, h => sorry
    -- | .isZeroSucc ht₁, .isZeroSucc ht₂ => sorry
    -- | .isZeroSucc ht₁, h => sorry
    -- | .isZero ht₁, .isZero ht₂ => sorry
    -- | .isZero ht₁, h => sorry

  /- 3.5.4 -/
  example {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂) (h₂: Eval₁ t₁ t₃): t₂ = t₃ := by
    induction h₁ with
      | iteTrue tru₁ fls₁ =>
        cases h₂ with
          | iteTrue tru₂ fls₂ => rfl
          | ite c₁ c₂ tru₂ fls₂ hc₂ => contradiction
      | iteFalse =>
        cases h₂ with
          | iteFalse tru₂ fls₂ => rfl
          | ite c₁ c₂ tru₂ fls₂ hc₂ => contradiction
      | ite c₁ c₂ tru₁ tru₂ hc₁ ih =>
        cases h₂ with
          | iteTrue tru₂ fls₂ => contradiction
          | iteFalse tru₂ fls₂ => contradiction
          | ite c₃ c₄ tru₂ fls₂ hc₂ => rw [_example hc₁ hc₂]
      -- | succ ht ih => sorry
      -- | predZero => sorry
      -- | predSucc hn => sorry
      -- | pred ht ih => sorry
      -- | isZeroZero => sorry
      -- | isZeroSucc ht => sorry
      -- | isZero ht ih => sorry

  /- 3.5.6 -/
  def Term.isNormal₁ (t₁: Term): Prop := ¬ ∃ t₂: Term, Eval₁ t₁ t₂

  /- 3.5.15 -/
  def Term.stuck₁ (t: Term): Prop := t.isNormal₁ ∧ ¬ Value t

  /- 3.5.7 -/
  theorem Value.normal₁ {t: Term}: Value t → t.isNormal₁ -- ¬ ∃ t₂: Term, Eval₁ t t₂
    | .true => sorry
    | .false => sorry

  example {t: Term} (h: Value t): t.isNormal₁ := by
    unfold Term.isNormal₁ Not
    intro h₁
    cases h with
      | true =>
        apply Exists.elim h₁
        · intro x h₂
          contradiction
      | false =>
        apply Exists.elim h₁
        · intro x h₂
          contradiction

  inductive Eval: Term → Term → Prop where
    | value (t: Term) (h: Value t): Eval t t
    | iteTrue (c t₁ t₂ f: Term) (h₁: Eval c Term.true) (h₂: Value t₂) (h₃: Eval t₁ t₂): Eval (.ite c t₁ f) t₂
    | iteFalse (c t f₁ f₂: Term) (h₁: Eval c Term.false) (h₂: Value f₂) (h₃: Eval f₁ f₂): Eval (.ite c t f₁) f₂
    -- | succ (t₁ t₂: Term) (h₁: Numeric t₂) (h₂: Eval t₁ t₂): Eval t₁.succ t₂.succ
    -- | predZero (t: Term) (h: Eval t Term.zero): Eval t.pred Term.zero
    -- | predSucc (t₁ t₂: Term) (h₁: Numeric t₂) (h₂: Eval t₁ t₂.succ): Eval t₁.pred t₂
    -- | isZeroZero (t₁: Term) (h: Eval t₁ .zero): Eval t₁.isZero .true
    -- | isZeroSucc (t₁ t₂: Term) (h₁: Numeric t₂) (h₂: Eval t₁ t₂.succ): Eval t₁.isZero .false

  /- 3.5.6 -/
  def Term.isNormal (t₁: Term): Prop := ¬ ∃ t₂: Term, Eval t₁ t₂
  /- 3.5.15 -/
  def Term.stuck (t: Term): Prop := t.isNormal ∧ ¬ Value t

  /- 3.5.9 -/
  theorem eval_rtc_eval₁ {t₁ t₂: Term}: RTC Eval₁ t₂ t₂ ↔ Eval t₁ t₂ := sorry

  /- 3.5.11 -/
  theorem normal_unique {t₁ t₂ t₃: Term} (ht₁: t₂.isNormal) (ht₂: t₂.isNormal): Eval t₁ t₂ → Eval t₂ t₃ → t₂ = t₃
    | .value .true _, .value .true _ => rfl
    | .value .false _, .value .false _ => rfl
    | _, _ => sorry

  example {t₁ t₂ t₃: Term} (ht₁: t₂.isNormal) (ht₂: t₂.isNormal) (he₁: Eval t₁ t₂) (he₂: Eval t₂ t₃): t₂ = t₃ := by
    induction he₁ with
      | value tm₁ hv₁ =>
        cases he₂ with
          | value tm₂ hv₂ => rfl
          | iteTrue c tru₁ tru₂ fls h₁ h₂ h₃ => sorry
          | iteFalse c tru fls₁ fls₂ h₁ h₂ h₃ => sorry
      | iteTrue => sorry
      | iteFalse => sorry

  /- 3.5.12 -/
  theorem Eval.termination {t₁: Term}: ∃ t₂: Term, t₂.isNormal → Eval t₁ t₂ := sorry

  theorem eval₁_eval₁ {t₁ t₂: Term}: Eval₁ t₁ t₂ ↔ t₁.eval₁ = t₂ := sorry
  theorem eval_eval {t₁ t₂: Term}: Eval t₁ t₂ ↔ t₁.eval = t₂ := sorry
end «Tapl».«UntypedArith»
