/-
# The Simply-Typed Lambda Calculus
-/

import SoftwareFoundations.LogicalFoundations.Maps
import SoftwareFoundations.ProgrammingLanguageFoundations.SmallStep

namespace SoftwareFoundations.ProgrammingLanguageFoundations.Stlc
  /-
  ## Overview
  -/

  /-
  ## Syntax
  -/

  /-
  ### Types
  -/

  inductive Ty: Type where
    | bool: Ty
    | arrow: Ty → Ty → Ty

  /-
  ### Terms
  -/

  inductive Term: Type where
    | var (id: String): Term
    | app (f: Term) (x: Term): Term
    | abs (id: String) (ty: Ty) (b: Term): Term
    | true: Term
    | false: Term
    | ite: Term → Term → Term → Term

  /-
  ### Grammar
  -/

  declare_syntax_cat stlc_ty

  syntax:max "𝔹" : stlc_ty
  syntax:50 stlc_ty:51 "→" stlc_ty:50 : stlc_ty
  syntax:max "‹" term "›" : stlc_ty

  syntax "(" stlc_ty ")" : stlc_ty

  syntax "[StlcTy| " stlc_ty "]" : term

  macro_rules
    | `([StlcTy| 𝔹])         => `(Ty.bool)
    | `([StlcTy| ‹$t:term›]) => `($(Lean.quote t))
    | `([StlcTy| $t₁ → $t₂]) => `(Ty.arrow [StlcTy| $t₁] [StlcTy| $t₂])
    | `([StlcTy| ( $ty ) ])  => `([StlcTy| $ty])

  example: [StlcTy| 𝔹] = Ty.bool := rfl
  example: [StlcTy| 𝔹 → 𝔹 → 𝔹 → 𝔹] = Ty.arrow .bool (.arrow .bool (.arrow .bool .bool)) := rfl
  example: [StlcTy| 𝔹 → (𝔹 → 𝔹) → 𝔹] = Ty.arrow .bool (.arrow (.arrow .bool .bool) .bool) := rfl

  declare_syntax_cat stlc

  syntax:max "tru" : stlc
  syntax:max "fls" : stlc
  syntax:max ident : stlc

  syntax:max "‹bool:" term "›" : stlc
  syntax:max "‹id:" term "›" : stlc
  syntax:max "‹" term "›" : stlc

  syntax:50 "λ" ident ":" stlc_ty "." stlc : stlc
  syntax:50 "λ" "‹" term "›" ":" stlc_ty "." stlc : stlc
  syntax:50 stlc:50 stlc:51 : stlc
  syntax:50 "ite" stlc "then" stlc "else" stlc : stlc

  syntax "(" stlc ")" : stlc

  syntax "[Stlc|" stlc "]" : term

  @[reducible]
  private def Term.ofBool: Bool → Term
    | .true => Term.true
    | .false => Term.false

  macro_rules
    | `([Stlc| tru])                             => `(Term.true)
    | `([Stlc| fls])                             => `(Term.false)
    | `([Stlc| $id:ident])                       => `(Term.var $(Lean.quote (toString id.getId)))
    | `([Stlc| ‹bool: $b:term ›])                => `(Term.ofBool $(Lean.quote b))
    | `([Stlc| ‹id: $b:term ›])                  => `(Term.var $(Lean.quote b))
    | `([Stlc| ‹$t:term› ])                      => `($(Lean.quote t))
    | `([Stlc| ite $c then $t else $f])          => `(Term.ite [Stlc| $c] [Stlc| $t] [Stlc| $f])
    | `([Stlc| $f $x])                           => `(Term.app [Stlc| $f] [Stlc| $x])
    | `([Stlc| λ $id : $ty:stlc_ty . $b])        => `(Term.abs $(Lean.quote (toString id.getId)) [StlcTy| $ty] [Stlc| $b])
    | `([Stlc| λ ‹$id:term› : $ty:stlc_ty . $b]) => `(Term.abs $(Lean.quote id) [StlcTy| $ty] [Stlc| $b])
    | `([Stlc| ( $c:stlc )])                     => `([Stlc| $c])

  example: [Stlc| tru] = Term.true := rfl
  example: [Stlc| fls] = Term.false := rfl
  example: [Stlc| ‹bool:true›] = Term.true := rfl
  example: [Stlc| ‹bool:false›] = Term.false := rfl
  example: [Stlc| ite tru then fls else tru] = Term.ite .true .false .true := rfl

  example: [Stlc| f x] = Term.app (.var "f") (.var "x") := rfl
  example: [Stlc| f x y z] = Term.app (.app (.app (.var "f") (.var "x")) (.var "y")) (.var "z") := rfl
  example: [Stlc| f (x y) z] = Term.app (.app (.var "f") (.app (.var "x") (.var "y"))) (.var "z") := rfl
  example: [Stlc| λ x: 𝔹. f x] = Term.abs "x" Ty.bool (.app (.var "f") (.var "x")) := rfl
  example: [Stlc| λ x: 𝔹. f x y] = Term.abs "x" Ty.bool (.app (.app (.var "f") (.var "x")) (.var "y")) := rfl

  example: [Stlc| (λ f: 𝔹 → 𝔹. λ x: 𝔹. f x) (λ x: 𝔹. x) tru] =
    Term.app
      (Term.app
        (Term.abs "f" (.arrow .bool .bool) (.abs "x" .bool (.app (.var "f") (.var "x"))))
        (Term.abs "x" .bool (.var "x")))
      Term.true
    := rfl

  example {id: String} {ty: Ty} {b: Term}: [Stlc| λ ‹id›: ‹ty›. ‹b›] = Term.abs id ty b := rfl

  /-
  ## Operational Semantics
  -/

  /-
  ### Values
  -/

  inductive Value: Term → Prop where
    | true: Value .true
    | false: Value .false
    | abs {id: String} {ty: Ty} {b: Term}: Value [Stlc| λ ‹id›: ‹ty›. ‹b›]

  /-
  ### Substitution
  -/

  def Term.subst (id: String) (s: Term): Term → Term
    | .var v =>
      if id = v
      then s
      else .var v
    | .abs v ty b =>
      if id = v
      then .abs v ty b
      else .abs v ty (subst id s b)
    | .app f x => .app (subst id s f) (subst id s x)
    | .true => .true
    | .false => .false
    | .ite c t f => .ite (subst id s c) (subst id s t) (subst id s f)

  notation "[" id "↦" s "]" t => Term.subst id s t

  example: (["x" ↦ [Stlc| tru]] [Stlc| x]) = [Stlc| tru] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| ite x then tru else fls]) = [Stlc| ite tru then tru else fls] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| x]) = [Stlc| tru] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| ite x then x else y]) = [Stlc| ite tru then tru else y] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| y]) = [Stlc| y] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| false]) = [Stlc| false] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| λ y: 𝔹. ite y then x else fls]) = [Stlc| λ y: 𝔹. ite y then tru else fls] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| λ y: 𝔹. x]) = [Stlc| λ y: 𝔹. tru] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| λ y: 𝔹. y]) = [Stlc| λ y: 𝔹. y] := rfl
  example: (["x" ↦ [Stlc| tru]] [Stlc| λ x: 𝔹. x]) = [Stlc| λ x: 𝔹. x] := rfl

  inductive Subst (id: String) (s: Term): Term → Term → Prop where

  namespace Term
    theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
  end Term

  namespace Tactic
    theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
  end Tactic

  namespace Blended
    theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
  end Blended

  /-
  ### Reduction
  -/

  inductive Eval₁: Term → Term → Prop where
    | appL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Stlc| ‹t₁› ‹t₃›] [Stlc| ‹t₂› ‹t₃›]
    | appR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Stlc| ‹v₁› ‹t₁›] [Stlc| ‹v₁› ‹t₂›]
    | appAbs {id: String} {ty: Ty} {b v: Term} (h₁: Value v): Eval₁ [Stlc| (λ ‹id›: ‹ty›. ‹b›) ‹v›] ([id ↦ v] [Stlc| ‹b›])
    | iteTrue {t f: Term}: Eval₁ [Stlc| ite tru then ‹t› else ‹f›] [Stlc| ‹t›]
    | iteFalse {t f: Term}: Eval₁ [Stlc| ite fls then ‹t› else ‹f›] [Stlc| ‹f›]
    | ite {c₁ c₂ t f: Term}: Eval₁ [Stlc| ite ‹c₁› then ‹t› else ‹f›] [Stlc| ite ‹c₂› then ‹t› else ‹f›]

  infix:50 "⟶" => Eval₁
  infix:50 "⇓" => SmallStep.MultiStep Eval₁

  /-
  ### Examples
  -/

  namespace Term
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)] ⇓ [Stlc| λ x: 𝔹. x] :=
      calc [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)]
        _ ⟶ [Stlc| λ x: 𝔹. x] := .appAbs .abs

    example: [Stlc| (λ x: 𝔹 → 𝔹. x) ((λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x))] ⇓ [Stlc| λ x: 𝔹. x] :=
      calc [Stlc| (λ x: 𝔹 → 𝔹. x) ((λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x))]
        _ ⟶ [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)] := .appR .abs (.appAbs .abs)
        _ ⟶ [Stlc| (λ x: 𝔹. x)]                 := .appAbs .abs

    example: [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. ite x then fls else tru) tru] ⇓ [Stlc| fls] :=
      calc [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. ite x then fls else tru) tru]
        _ ⟶ [Stlc| (λ x: 𝔹. ite x then fls else tru) tru] := .appL (.appAbs .abs)
        _ ⟶ [Stlc| ite tru then fls else tru]             := .appAbs .true
        _ ⟶ [Stlc| fls]                                   := .iteTrue

    example: [Stlc| (λ x: 𝔹 → 𝔹. x) ((λ x: 𝔹. ite x then fls else tru) tru)] ⇓ [Stlc| fls] :=
      calc [Stlc| (λ x: 𝔹 → 𝔹. x) ((λ x: 𝔹. ite x then fls else tru) tru)]
        _ ⟶ [Stlc| (λ x: 𝔹 → 𝔹. x) (ite tru then fls else tru)] := .appR .abs (.appAbs .abs)
        _ ⟶ [Stlc| (λ x: 𝔹 → 𝔹. x) fls]                         := .appR .abs .iteTrue
        _ ⟶ [Stlc| fls]                                         := .appAbs .false

    example: [Stlc| (λ x: 𝔹 → 𝔹 → 𝔹 → 𝔹. x) (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)] ⇓ [Stlc| (λ x: 𝔹. x)] :=
      calc [Stlc| (λ x: 𝔹 → 𝔹 → 𝔹 → 𝔹. x) (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)]
        _ ⟶ [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)] := .appL (.appAbs .abs)
        _ ⟶ [Stlc| (λ x: 𝔹. x)]                 := .appAbs .abs
  end Term

  namespace Tactic
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)] ⇓ [Stlc| λ x: 𝔹. x] := by sorry
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) ((λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x))] ⇓ [Stlc| λ x: 𝔹. x] := by sorry
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. ite x then fls else tru) tru] ⇓ [Stlc| fls] := by sorry
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) ((λ x: 𝔹. ite x then fls else tru) tru)] ⇓ [Stlc| fls] := by sorry
    example: [Stlc| (λ x: 𝔹 → 𝔹 → 𝔹 → 𝔹. x) (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)] ⇓ [Stlc| (λ x: 𝔹. x)] := by sorry
  end Tactic

  namespace Blended
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)] ⇓ [Stlc| λ x: 𝔹. x] := sorry
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) ((λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x))] ⇓ [Stlc| λ x: 𝔹. x] := sorry
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. ite x then fls else tru) tru] ⇓ [Stlc| fls] := sorry
    example: [Stlc| (λ x: 𝔹 → 𝔹. x) ((λ x: 𝔹. ite x then fls else tru) tru)] ⇓ [Stlc| fls] := sorry
    example: [Stlc| (λ x: 𝔹 → 𝔹 → 𝔹 → 𝔹. x) (λ x: 𝔹 → 𝔹. x) (λ x: 𝔹. x)] ⇓ [Stlc| (λ x: 𝔹. x)] := sorry
  end Blended

  /-
  ## Typing
  -/

  open SoftwareFoundations.LogicalFoundations.Maps

  /-
  ### Contexts
  -/

  def Context: Type := PartialMap Ty
  def Context.empty: PartialMap Ty := PartialMap.empty

  /-
  ### Typing Relation
  -/

  inductive HasType: Context → Term → Ty → Prop where
    | var {Γ: Context} {id: String} {ty: Ty} (h₁: Γ id = .some ty): HasType Γ [Stlc| ‹id:id›] ty
    | abs {Γ: Context} {id: String} {ty₁ ty₂: Ty} {b: Term} (h₁: HasType (Γ.update id ty₁) b ty₁): HasType Γ [Stlc| λ ‹id›: ‹ty₁›. ‹b›] [StlcTy| ‹ty₁› → ‹ty₂›]
    | app {Γ: Context} {f x: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ f [StlcTy| ‹ty₁› → ‹ty₂›]) (h₂: HasType Γ x ty₁): HasType Γ [Stlc| ‹f› ‹x›] ty₂
    | true {Γ: Context}: HasType Γ .true .bool
    | false {Γ: Context}: HasType Γ .false .bool
    | ite {Γ: Context} {c t f: Term} {ty: Ty} (h₁: HasType Γ c .bool) (h₂: HasType Γ t ty) (h₃: HasType Γ f ty): HasType Γ [Stlc| ite ‹c› then ‹t› else ‹f›] ty

  notation ctx "⊢" t ":" ty => HasType ctx t ty

  /-
  ### Examples
  -/

  namespace Term
    example: Context.empty ⊢ [Stlc| λ x: 𝔹. x] : [StlcTy| 𝔹 → 𝔹] :=
      have h := PartialMap.updateEq Context.empty "x" .bool
      .abs (.var h)

    example: Context.empty ⊢ [Stlc| λ x: 𝔹. λ y: 𝔹 → 𝔹. y (y x)] : [StlcTy| 𝔹 → (𝔹 → 𝔹) → 𝔹] :=
      have h₁ := PartialMap.updateEq Context.empty "x" .bool
      have h₂ := PartialMap.updateEq (Context.empty.update "x" .bool) "y" [StlcTy| 𝔹 → 𝔹]
      -- .abs (.abs (.app (.app _ _)))
      sorry

    example: ∃ ty: Ty, Context.empty ⊢ [Stlc| λ x: 𝔹 → 𝔹. λ y: 𝔹 → 𝔹. λ z: 𝔹. y (x z)] : ty := sorry
    example: ¬ ∃ ty: Ty, Context.empty ⊢ [Stlc| λ x: 𝔹. λ y: 𝔹. x y] : ty := sorry
    example: ¬ ∃ ty₁ ty₂: Ty, Context.empty ⊢ [Stlc| λ x: ‹ty₁›. x x] : ty₂ := sorry
  end Term

  namespace Tactic
    example: Context.empty ⊢ [Stlc| λ x: 𝔹. x] : [StlcTy| 𝔹 → 𝔹] := by sorry
    example: Context.empty ⊢ [Stlc| λ x: 𝔹. λ y: 𝔹 → 𝔹. y (y x)] : [StlcTy| 𝔹 → (𝔹 → 𝔹) → 𝔹] := by sorry
    example: ∃ ty: Ty, Context.empty ⊢ [Stlc| λ x: 𝔹 → 𝔹. λ y: 𝔹 → 𝔹. λ z: 𝔹. y (x z)] : ty := by sorry
    example: ¬ ∃ ty: Ty, Context.empty ⊢ [Stlc| λ x: 𝔹. λ y: 𝔹. x y] : ty := by sorry
    example: ¬ ∃ ty₁ ty₂: Ty, Context.empty ⊢ [Stlc| λ x: ‹ty₁›. x x] : ty₂ := by sorry
  end Tactic

  namespace Blended
    example: Context.empty ⊢ [Stlc| λ x: 𝔹. x] : [StlcTy| 𝔹 → 𝔹] := sorry
    example: Context.empty ⊢ [Stlc| λ x: 𝔹. λ y: 𝔹 → 𝔹. y (y x)] : [StlcTy| 𝔹 → (𝔹 → 𝔹) → 𝔹] := sorry
    example: ∃ ty: Ty, Context.empty ⊢ [Stlc| λ x: 𝔹 → 𝔹. λ y: 𝔹 → 𝔹. λ z: 𝔹. y (x z)] : ty := sorry
    example: ¬ ∃ ty: Ty, Context.empty ⊢ [Stlc| λ x: 𝔹. λ y: 𝔹. x y] : ty := sorry
    example: ¬ ∃ ty₁ ty₂: Ty, Context.empty ⊢ [Stlc| λ x: ‹ty₁›. x x] : ty₂ := sorry
  end Blended
end SoftwareFoundations.ProgrammingLanguageFoundations.Stlc
