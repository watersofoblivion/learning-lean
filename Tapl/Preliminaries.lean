/-
# Mathematical Preleminaries
-/

import Mathlib.Init.Set

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace «Tapl»

  /-
  ## Sets, Relations, and Functions
  -/

  /- 2.1.7 -/
  def domain {y: β} (R: α → β → Prop): Set α := { x | R x y }
  def range {x: α} (R: α → β → Prop): Set β := { y | R x y }

  /- 2.1.8 -/
  def partialFunction (R: α → β → Prop): Prop := ∀ x: α, ∀ y₁ y₂: β, R x y₁ → R x y₂ → y₁ = y₂
  -- def totalFunction (R: α → β → Prop): Prop := ∀ a: α, partialFunction R ∧ a ∈ domain R

  /- 2.1.9 -/
  -- def defined (R: α → β → Prop): Prop := ∀ a: α, a ∈ domain R

  /- 2.1.10 -/
  def preserves (P: α → Prop) (R: α → α → Prop): Prop := ∀ x₁ x₂: α, P x₁ → R x₁ x₂ → P x₂

  /-
  ## Ordered Sets
  -/

  /- 2.2.1 -/
  def reflexive (R: α → α → Prop): Prop := ∀ x: α, R x x
  def symmetric (R: α → α → Prop): Prop := ∀ x₁ x₂: α, R x₁ x₂ → R x₂ x₁
  def transitive (R: α → α → Prop): Prop := ∀ x₁ x₂ x₃: α, R x₁ x₂ → R x₂ x₃ → R x₁ x₃
  def antisymmetric (R: α → α → Prop): Prop := ∀ x₁ x₂: α, R x₁ x₂ → R x₂ x₁ → x₁ = x₂

  /- 2.2.2 -/
  def preorder (R: α → α → Prop): Prop := reflexive R ∧ transitive R

  /- 2.2.2 -/
  def partialOrder (R: α → α → Prop): Prop := preorder R ∧ antisymmetric R

  /- 2.2.3 -/


  /- 2.2.4 -/
  def equivalence (R: α → α → Prop): Prop := reflexive R ∧ transitive R ∧ symmetric R

  /- 2.2.5 -/
  inductive RC (R: α → α → Prop): α → α → Prop where
    | base (x₁ x₂: α): R x₁ x₂ → RC R x₁ x₂
    | refl (x: α): RC R x x

  /- 2.2.5 -/
  inductive TC (R: α → α → Prop): α → α → Prop where
    | base (x₁ x₂: α): R x₁ x₂ → TC R x₁ x₂
    | trans (x₁ x₂ x₃: α): TC R x₁ x₂ → TC R x₂ x₃ → TC R x₁ x₃

  /- 2.2.5 -/
  inductive RTC (R: α → α → Prop): α → α → Prop where
    | base (x₁ x₂: α): R x₁ x₂ → RTC R x₁ x₂
    | refl (x: α): R x x → RTC R x x
    | trans (x₁ x₂ x₃: α): RTC R x₁ x₂ → RTC R x₂ x₃ → RTC R x₁ x₃

  /- 2.2.6 -/

  /- 2.2.7 -/

  /- 2.2.8 -/

  /- 2.2.9 -/

  /- 2.2.10 -/

  /-
  ## Sequences
  -/

  /- 2.3.1 -/

  /-
  ## Induction
  -/

  /- 2.4.1 -/

  /- 2.4.2 -/

  /- 2.4.3 -/

  /- 2.4.4 -/

  /-
  ## Deterministic Relations
  -/

  def deterministic (R: α → α → Prop) (x₁ x₂ x₃: α): R x₁ x₂ → R x₁ x₃ → x₂ = x₃ := sorry
end «Tapl»
