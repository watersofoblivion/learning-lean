/-
# Mathematical Preleminaries
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace «Tapl»

  /-
  ## Sets, Relations, and Functions
  -/


  /-
  ## Reflexive, Transitive Closure
  -/

  inductive RTC (R: α → α → Prop): α → α → Prop where
    | base: ∀ x₁ x₂: α, R x₁ x₂ → RTC R x₁ x₂
    | refl: ∀ x: α, R x x → RTC R x x
    | trans: ∀ x₁ x₂ x₃: α, RTC R x₁ x₂ → RTC R x₂ x₃ → RTC R x₁ x₃

  /-
  ## Deterministic Relations
  -/

  def deterministic (R: α → α → Prop) (x₁ x₂ x₃: α): R x₁ x₂ → R x₁ x₃ → x₂ = x₃ := sorry
end «Tapl»
