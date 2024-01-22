/-
# Properties of Relations
-/

/-
## Relations
-/

def Relation (α: Type): Type := α → α → Prop

inductive Le: Nat → Nat → Prop where
  | eq (n: Nat): Le n n
  | less (n₁ n₂: Nat) (h: Le n₁ n₂): Le n₁ n₂.succ

#print Le
#check (Le: Nat → Nat → Prop)
#check (Le: Relation Nat)
#check Le.recOn

/-
## Basic Properties
-/

/-
### Partial Functions
-/

def PartialFunction (R: Relation α): Prop := ∀ x y₁ y₂: α, R x y₁ → R x y₂ → y₁ = y₂

inductive NextNat: Relation Nat where
  | next (n: Nat): NextNat n n.succ

#check (NextNat: Relation Nat)

theorem NextNat.partial_function: PartialFunction NextNat := by
  unfold PartialFunction
  intro x y₁ y₂ h₁ h₂
  cases h₁ with
    | next n₁ =>
      cases h₂ with
        | next n₂ => simp

-- example: PartialFunction NextNat
--   | x, y₁, .succ y₂, .next n₁, .next n₂ => sorry

theorem Le.not_partial_function: ¬PartialFunction Le := by
  unfold Not
  unfold PartialFunction
  intro h
  have h₁: 0 = 1 := by
    apply h 0
    · exact Le.eq 0
    · apply Le.less
      · apply Le.eq
  contradiction

-- example: ¬PartialFunction Le :=
--   fun h =>
--     have h₃: 0 = 1 := h 0 0 1 Le.eq (Le.less 1 Le.eq)
--     absurd (0 = 0) (0 = 1)

namespace Duplicated
  inductive TotalRelation: Nat → Nat → Prop where
    | related (n₁ n₂: Nat): TotalRelation n₁ n₂

  theorem TotalRelation.not_partial_function: ¬PartialFunction TotalRelation := by
    unfold Not
    unfold PartialFunction
    intro h
    have h₁: 0 = 1 := by
      apply h 0
      · exact TotalRelation.related 0 0
      . exact TotalRelation.related 0 1
    contradiction

  example: ¬PartialFunction TotalRelation := sorry

  inductive EmptyRelation: Nat → Nat → Prop

  theorem EmptyRelation.partial_function: PartialFunction EmptyRelation := by
    unfold PartialFunction
    intro x y₁ y₂ h₁
    cases h₁

  -- example: PartialFunction EmptyRelation
  --   | x, y₁, y₂, _, _ => sorry
end Duplicated

/-
### Reflexive Relations
-/

def ReflexiveR (R: Relation α): Prop := ∀ x: α, R x x

theorem Le.reflexive: ReflexiveR Le := by
  unfold ReflexiveR
  intro x
  exact Le.eq x

example: ReflexiveR Le
  | n => Le.eq n

/-
### Transitive Relations
-/

def TransitiveR (R: Relation α): Prop := ∀ x₁ x₂ x₃: α, R x₁ x₂ → R x₂ x₃ → R x₁ x₃

theorem Le.transitive: TransitiveR Le := by
  unfold TransitiveR
  intro x₁ x₂ x₃ h₁ h₂
  induction h₁ with
    | eq => exact h₂
    | less n₁ h₃ ih =>
      cases h₂ with
        | eq => sorry
        | less n₂ h₄ => sorry

example: TransitiveR Le
  | x₁, x₂, x₃, _, _ => sorry

-- TODO: Extra theorems

/-
### Symmetric and Antisymmetric Relations
-/

def SymmetricR (R: Relation α): Prop := ∀ x₁ x₂: α, R x₁ x₂ → R x₂ x₁

theorem Le.not_symmetric: ¬SymmetricR Le := by
  unfold Not
  unfold SymmetricR
  intro h
  have h₁: Le 1 0 :=
    Le.eq 0
      |> Le.less 0 0
      |> h 0 1
  contradiction

example: ¬SymmetricR Le
  | h =>
    have h₁: Le 1 0 :=
      Le.eq 0
        |> Le.less 0 0
        |> h 0 1
    sorry

def AntisymmetricR (R: Relation α): Prop := ∀ x₁ x₂: α, R x₁ x₂ → R x₂ x₁ → x₁ = x₂

theorem Le.antisymmetric: AntisymmetricR Le := by
  unfold AntisymmetricR
  intro x₁ x₂ h₁ h₂
  induction h₁ with
    | eq => rfl
    | less n₁ h₃ ih =>
      cases h₂ with
        | eq => rfl
        | less n₂ h₄ => sorry

example: AntisymmetricR Le
  | x₁, x₂, h₁, h₂ => sorry

-- TODO: Other examples

/-
### Equivalence Relations
-/

def EquivalenceR (R: Relation α): Prop := ReflexiveR R ∧ SymmetricR R ∧ TransitiveR R

/-
### Partial Orders and Preorders
-/

namespace Duplicated
  def PartialOrder (R: Relation α): Prop := ReflexiveR R ∧ AntisymmetricR R ∧ TransitiveR R
  def Preorder (R: Relation α): Prop := ReflexiveR R ∧ TransitiveR R

  theorem Le.partial_order: PartialOrder Le := by
    unfold PartialOrder
    apply And.intro
    · exact Le.reflexive
    · apply And.intro
      · exact Le.antisymmetric
      · exact Le.transitive

  example: PartialOrder Le :=
    ⟨Le.reflexive, Le.antisymmetric, Le.transitive⟩
end Duplicated

/-
## Reflexive Transitive Closure
-/

inductive RTC (R: Relation α): Relation α where
  | base (x₁ x₂: α) (h: R x₁ x₂): RTC R x₁ x₂
  | refl (x: α): RTC R x x
  | trans (x₁ x₂ x₃: α) (h₁: RTC R x₁ x₂) (h₂: RTC R x₂ x₃): RTC R x₁ x₃

theorem NextNat.rtc_le (n₁ n₂: Nat): Le n₁ n₂ ↔ RTC NextNat n₁ n₂ := by
  apply Iff.intro
  · intro h
    induction h with
      | eq => sorry
      | less n h ih => sorry
  · intro h
    induction h with
      | base x₁ x₂ h => sorry
      | refl x => exact Le.eq x
      | trans x₁ x₂ x₃ h₁ h₂ ih₁ ih₂ => sorry

example (n₁ n₂: Nat): Le n₁ n₂ ↔ RTC NextNat n₁ n₂ :=
  ⟨mp, mpr⟩
  where
    mp: Le n₁ n₂ → RTC NextNat n₁ n₂
      | .eq _ => sorry
      | .less _ _ h => sorry
    mpr: RTC NextNat n₁ n₂ → Le n₁ n₂
      | .base _ _ (.next _) => sorry -- Le.less n₁ n₂ (Le.eq n₁ n₁)
      | .refl _ => Le.eq n₁
      | .trans _ _ _ h₁ h₂ => sorry

/-
Lean doesn't allow this type of inductive definition, while Coq does.  The
remaining exercies are therefore moot.
-/
-- inductive RTC₂ (R: Relation α) (x: α): α → Prop where
--   | refl: RTC₂ R x x
--   | trans (x₁ x₂: α) (h₁: R x x₁) (h₂: RTC₂ R x x₁) (h₃: RTC₂ R x₁ x₂): RTC₂ R x x₂

-- Just to have something after the comment to make the parser happy
#check Nat
