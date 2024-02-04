/-
# Properties of the Simply-Typed Lambda Calculus
-/

import SoftwareFoundations.LogicalFoundations.Maps
import SoftwareFoundations.ProgrammingLanguageFoundations.SmallStep
import SoftwareFoundations.ProgrammingLanguageFoundations.Stlc

namespace SoftwareFoundations.ProgrammingLanguageFoundations.Stlc
  /-
  ## Canonical Forms
  -/

  namespace Term
    theorem Canonical.bool {t: Term}: (● ⊢ [Stlc| ‹t›] : [StlcTy| 𝔹]) → Value t → (t = [Stlc| tru]) ∨ (t = [Stlc| fls])
      | .true, _ => .inl rfl
      | .false, _ => .inr rfl

    theorem Canonical.fun {t: Term} {ty₁ ty₂: Ty}: (● ⊢ [Stlc| ‹t›] : [StlcTy| ‹ty₁› → ‹ty₂›]) → Value t → ∃ id: String, ∃ b: Term, t = [Stlc| λ ‹id›: ‹ty₁›. ‹b›]
      | .abs h₁, .abs =>
        have h := sorry
        ⟨"x", ⟨[Stlc| x], h⟩⟩
  end Term

  namespace Tactic
  end Tactic

  namespace Blended
  end Blended

  /-
  ## Progress
  -/

  namespace Term
    theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
  end Term

  namespace Tactic
    -- Induction on Typing
    theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, t₁ ⟶ t₂ := by sorry

    -- Induction on Terms instead of Typing
    example {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, t₁ ⟶ t₂ := by sorry
  end Tactic

  namespace Blended
    theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
  end Blended

  /-
  ## Preservation
  -/

  /-
  ### The Weakening Lemma
  -/

  namespace Term
    theorem Context.weakening {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: Γ₁.includedIn Γ₂ → (Γ₁ ⊢ t : ty) → (Γ₂ ⊢ t : ty) := sorry
    theorem Context.weakening.empty {Γ: Context} {t: Term} {ty: Ty}: (● ⊢ t : ty) → (Γ ⊢ t : ty) := sorry
  end Term

  namespace Tactic
    theorem Context.weakening {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: Γ₁.includedIn Γ₂ → (Γ₁ ⊢ t : ty) → (Γ₂ ⊢ t : ty) := by sorry
    theorem Context.weakening.empty {Γ: Context} {t: Term} {ty: Ty}: (● ⊢ t : ty) → (Γ ⊢ t : ty) := by sorry
  end Tactic

  namespace Blended
    theorem Context.weakening {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: Γ₁.includedIn Γ₂ → (Γ₁ ⊢ t : ty) → (Γ₂ ⊢ t : ty) := sorry
    theorem Context.weakening.empty {Γ: Context} {t: Term} {ty: Ty}: (● ⊢ t : ty) → (Γ ⊢ t : ty) := sorry
  end Blended

  /-
  ### The Substitution Lemma
  -/

  namespace Term
    theorem Term.subst.preservation {Γ: Context} {id: String} {t₁ t₂: Term} {ty₁ ty₂: Ty}: (Γ.update id ty₁ ⊢ t₁ : ty₂) → (● ⊢ t₂ : ty₂) → Γ ⊢ (Term.subst id t₂ t₁) : ty₂ := sorry
  end Term

  namespace Tactic
    -- Induction on Typing
    theorem Term.subst.preservation {Γ: Context} {id: String} {t₁ t₂: Term} {ty₁ ty₂: Ty}: (Γ.update id ty₁ ⊢ t₁ : ty₂) → (● ⊢ t₂ : ty₂) → Γ ⊢ (Term.subst id t₂ t₁) : ty₂ := by sorry
    -- Induction on Terms instead of Typing
    example {Γ: Context} {id: String} {t₁ t₂: Term} {ty₁ ty₂: Ty}: (Γ.update id ty₁ ⊢ t₁ : ty₂) → (● ⊢ t₂ : ty₂) → Γ ⊢ (Term.subst id t₂ t₁) : ty₂ := by sorry
  end Tactic

  namespace Blended
    theorem Term.subst.preservation {Γ: Context} {id: String} {t₁ t₂: Term} {ty₁ ty₂: Ty}: (Γ.update id ty₁ ⊢ t₁ : ty₂) → (● ⊢ t₂ : ty₂) → Γ ⊢ (Term.subst id t₂ t₁) : ty₂ := sorry
  end Blended

  /-
  ### Main Theorem
  -/

  namespace Term
    theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := sorry

    example: ∃ t₁ t₂: Term, ∃ ty: Ty, (t₁ ⟶ t₂) ∧ (● ⊢ t₂ : ty) ∧ ¬ (● ⊢ t₁ : ty) := sorry
  end Term

  namespace Tactic
    theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := by sorry

    example: ∃ t₁ t₂: Term, ∃ ty: Ty, (t₁ ⟶ t₂) ∧ (● ⊢ t₂ : ty) ∧ ¬ (● ⊢ t₁ : ty) := by sorry
  end Tactic

  namespace Blended
    theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := sorry

    example: ∃ t₁ t₂: Term, ∃ ty: Ty, (t₁ ⟶ t₂) ∧ (● ⊢ t₂ : ty) ∧ ¬ (● ⊢ t₁ : ty) := sorry
  end Blended

  /-
  ## Type Soundness
  -/

  def Term.normal: Term → Prop := SmallStep.Relation.normal Eval₁
  def Term.stuck (t: Term): Prop := t.normal ∧ ¬ Value t

  namespace Term
    theorem HasType.sound {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → ¬ t₂.stuck := sorry
  end Term

  namespace Tactic
    theorem HasType.sound {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → ¬ t₂.stuck := by sorry
  end Tactic

  namespace Blended
    theorem HasType.sound {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → ¬ t₂.stuck := sorry
  end Blended

  /-
  ## Uniqueness of Types
  -/

  namespace Term
    theorem HasType.unique {Γ: Context} {t: Term} {ty₁ ty₂: Ty}: (Γ ⊢ t : ty₁) → (Γ ⊢ t : ty₂) → ty₁ = ty₂ := sorry
  end Term

  namespace Tactic
    theorem HasType.unique {Γ: Context} {t: Term} {ty₁ ty₂: Ty}: (Γ ⊢ t : ty₁) → (Γ ⊢ t : ty₂) → ty₁ = ty₂ := by sorry
  end Tactic

  namespace Blended
    theorem HasType.unique {Γ: Context} {t: Term} {ty₁ ty₂: Ty}: (Γ ⊢ t : ty₁) → (Γ ⊢ t : ty₂) → ty₁ = ty₂ := sorry
  end Blended

  /-
  ## Context Invariance
  -/

  inductive FreeIn (id: String): Term → Prop where
    | var: FreeIn id [Stlc| ‹id:x›]
    | appL {t₁ t₂: Term} (h₁: FreeIn id t₁): FreeIn id [Stlc| ‹t₁› ‹t₂›]
    | appR {t₁ t₂: Term} (h₁: FreeIn id t₂): FreeIn id [Stlc| ‹t₁› ‹t₂›]
    | abs {var: String} {t: Term} {ty: Ty} (h₁: id ≠ var) (h₂: FreeIn id t): FreeIn id [Stlc| λ ‹y›: ‹ty›. ‹t›]
    | iteC {c t f: Term} (h₁: FreeIn id c): FreeIn id [Stlc| ite ‹c› then ‹t› else ‹f›]
    | iteT {c t f: Term} (h₁: FreeIn id t): FreeIn id [Stlc| ite ‹c› then ‹t› else ‹f›]
    | iteF {c t f: Term} (h₁: FreeIn id f): FreeIn id [Stlc| ite ‹c› then ‹t› else ‹f›]

  def Term.closed (t: Term): Prop := ∀ id: String, ¬ FreeIn id t

  namespace Term
    theorem Context.freeIn {id: String} {t: Term} {ty₁: Ty} {Γ: Context}: (FreeIn id t) → (Γ ⊢ t : ty₁) → ∃ ty₂: Ty, Γ id = .some ty₂ := sorry
    theorem Context.empty.hasType.closed {t: Term} {ty: Ty}: (● ⊢ t : ty) → t.closed := sorry
    theorem Context.invariance {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: (Γ₁ ⊢ t : ty) → (∀ id: String, FreeIn id t → Γ₁ id = Γ₂ id) → Γ₂ ⊢ t : ty := sorry
  end Term

  namespace Tactic
    theorem Context.freeIn {id: String} {t: Term} {ty₁: Ty} {Γ: Context}: (FreeIn id t) → (Γ ⊢ t : ty₁) → ∃ ty₂: Ty, Γ id = .some ty₂ := by sorry
    theorem Context.empty.hasType.closed {t: Term} {ty: Ty}: (● ⊢ t : ty) → t.closed := by sorry
    theorem Context.invariance {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: (Γ₁ ⊢ t : ty) → (∀ id: String, FreeIn id t → Γ₁ id = Γ₂ id) → Γ₂ ⊢ t : ty := by sorry
  end Tactic

  namespace Blended
    theorem Context.freeIn {id: String} {t: Term} {ty₁: Ty} {Γ: Context}: (FreeIn id t) → (Γ ⊢ t : ty₁) → ∃ ty₂: Ty, Γ id = .some ty₂ := sorry
    theorem Context.empty.hasType.closed {t: Term} {ty: Ty}: (● ⊢ t : ty) → t.closed := sorry
    theorem Context.invariance {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: (Γ₁ ⊢ t : ty) → (∀ id: String, FreeIn id t → Γ₁ id = Γ₂ id) → Γ₂ ⊢ t : ty := sorry
  end Blended

  /-
  ## Additional Exercises
  -/

  namespace Variation₁
    open LogicalFoundations.Maps

    inductive Term: Type where
      | var (id: String): Term
      | app (f: Term) (x: Term): Term
      | abs (id: String) (ty: Ty) (b: Term): Term
      | true: Term
      | false: Term
      | ite: Term → Term → Term → Term
      | zap: Term

    declare_syntax_cat stlc_zap

    syntax:max "tru" : stlc_zap
    syntax:max "fls" : stlc_zap
    syntax:max "zap" : stlc_zap
    syntax:max ident : stlc_zap

    syntax:max "‹bool:" term "›" : stlc_zap
    syntax:max "‹id:" term "›" : stlc_zap
    syntax:max "‹" term "›" : stlc_zap

    syntax:50 "λ" ident ":" stlc_ty "." stlc_zap : stlc_zap
    syntax:50 "λ" "‹" term "›" ":" stlc_ty "." stlc_zap : stlc_zap
    syntax:50 stlc_zap:50 stlc_zap:51 : stlc_zap
    syntax:50 "ite" stlc_zap "then" stlc_zap "else" stlc_zap : stlc_zap

    syntax "(" stlc_zap ")" : stlc_zap

    syntax "[StlcZap|" stlc_zap "]" : term

    @[reducible]
    private def Term.ofBool: Bool → Term
      | .true => Term.true
      | .false => Term.false

    macro_rules
      | `([StlcZap| tru])                             => `(Term.true)
      | `([StlcZap| fls])                             => `(Term.false)
      | `([StlcZap| zap])                             => `(Term.zap)
      | `([StlcZap| $id:ident])                       => `(Term.var $(Lean.quote (toString id.getId)))
      | `([StlcZap| ‹bool: $b:term ›])                => `(Term.ofBool $(Lean.quote b))
      | `([StlcZap| ‹id: $b:term ›])                  => `(Term.var $(Lean.quote b))
      | `([StlcZap| ‹$t:term› ])                      => `($(Lean.quote t))
      | `([StlcZap| ite $c then $t else $f])          => `(Term.ite [StlcZap| $c] [StlcZap| $t] [StlcZap| $f])
      | `([StlcZap| $f $x])                           => `(Term.app [StlcZap| $f] [StlcZap| $x])
      | `([StlcZap| λ $id : $ty:stlc_ty . $b])        => `(Term.abs $(Lean.quote (toString id.getId)) [StlcTy| $ty] [StlcZap| $b])
      | `([StlcZap| λ ‹$id:term› : $ty:stlc_ty . $b]) => `(Term.abs $(Lean.quote id) [StlcTy| $ty] [StlcZap| $b])
      | `([StlcZap| ( $c:stlc_zap )])                 => `([StlcZap| $c])

    inductive Value: Term → Prop where
      | true: Value .true
      | false: Value .false
      | abs {id: String} {ty: Ty} {b: Term}: Value [StlcZap| λ ‹id›: ‹ty›. ‹b›]

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
      | .zap => .zap
      | .ite c t f => .ite (subst id s c) (subst id s t) (subst id s f)

    scoped notation "[" id "↦" s "]" t => Term.subst id s t

    inductive Subst (id: String) (s: Term): Term → Term → Prop where

    namespace Term
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
    end Term

    namespace Tactic
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := by sorry
    end Tactic

    namespace Blended
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
    end Blended

    inductive Eval₁: Term → Term → Prop where
      | appL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [StlcZap| ‹t₁› ‹t₃›] [StlcZap| ‹t₂› ‹t₃›]
      | appR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [StlcZap| ‹v₁› ‹t₁›] [StlcZap| ‹v₁› ‹t₂›]
      | appAbs {id: String} {ty: Ty} {b v: Term} (h₁: Value v): Eval₁ [StlcZap| (λ ‹id›: ‹ty›. ‹b›) ‹v›] ([id ↦ v] [StlcZap| ‹b›])
      | iteTrue {t f: Term}: Eval₁ [StlcZap| ite tru then ‹t› else ‹f›] [StlcZap| ‹t›]
      | iteFalse {t f: Term}: Eval₁ [StlcZap| ite fls then ‹t› else ‹f›] [StlcZap| ‹f›]
      | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [StlcZap| ite ‹c₁› then ‹t› else ‹f›] [StlcZap| ite ‹c₂› then ‹t› else ‹f›]
      | zap {t: Term}: Eval₁ t [StlcZap| zap]

    scoped infix:50 "⟶" => Eval₁
    scoped infix:50 "⇓" => SmallStep.MultiStep Eval₁

    def Context: Type := PartialMap Ty
    def Context.empty: PartialMap Ty := PartialMap.empty

    scoped notation "●" => Context.empty

    inductive HasType: Context → Term → Ty → Prop where
      | var {Γ: Context} {id: String} {ty: Ty} (h₁: Γ id = .some ty): HasType Γ [StlcZap| ‹id:id›] ty
      | abs {Γ: Context} {id: String} {ty₁ ty₂: Ty} {b: Term} (h₁: HasType (Γ.update id ty₁) b ty₁): HasType Γ [StlcZap| λ ‹id›: ‹ty₁›. ‹b›] [StlcTy| ‹ty₁› → ‹ty₂›]
      | app {Γ: Context} {f x: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ f [StlcTy| ‹ty₁› → ‹ty₂›]) (h₂: HasType Γ x ty₁): HasType Γ [StlcZap| ‹f› ‹x›] ty₂
      | true {Γ: Context}: HasType Γ .true .bool
      | false {Γ: Context}: HasType Γ .false .bool
      | ite {Γ: Context} {c t f: Term} {ty: Ty} (h₁: HasType Γ c .bool) (h₂: HasType Γ t ty) (h₃: HasType Γ f ty): HasType Γ [StlcZap| ite ‹c› then ‹t› else ‹f›] ty
      | zap {Γ: Context} {ty: Ty}: HasType Γ [StlcZap| zap] ty

    scoped notation ctx "⊢" t ":" ty => HasType ctx t ty
  end Variation₁

  namespace Variation₂
    open LogicalFoundations.Maps

    inductive Term: Type where
      | var (id: String): Term
      | app (f: Term) (x: Term): Term
      | abs (id: String) (ty: Ty) (b: Term): Term
      | true: Term
      | false: Term
      | ite: Term → Term → Term → Term
      | foo: Term

    declare_syntax_cat stlc_foo

    syntax:max "tru" : stlc_foo
    syntax:max "fls" : stlc_foo
    syntax:max "foo" : stlc_foo
    syntax:max ident : stlc_foo

    syntax:max "‹bool:" term "›" : stlc_foo
    syntax:max "‹id:" term "›" : stlc_foo
    syntax:max "‹" term "›" : stlc_foo

    syntax:50 "λ" ident ":" stlc_ty "." stlc_foo : stlc_foo
    syntax:50 "λ" "‹" term "›" ":" stlc_ty "." stlc_foo : stlc_foo
    syntax:50 stlc_foo:50 stlc_foo:51 : stlc_foo
    syntax:50 "ite" stlc_foo "then" stlc_foo "else" stlc_foo : stlc_foo

    syntax "(" stlc_foo ")" : stlc_foo

    syntax "[StlcFoo|" stlc_foo "]" : term

    @[reducible]
    private def Term.ofBool: Bool → Term
      | .true => Term.true
      | .false => Term.false

    macro_rules
      | `([StlcFoo| tru])                             => `(Term.true)
      | `([StlcFoo| fls])                             => `(Term.false)
      | `([StlcFoo| foo])                             => `(Term.foo)
      | `([StlcFoo| $id:ident])                       => `(Term.var $(Lean.quote (toString id.getId)))
      | `([StlcFoo| ‹bool: $b:term ›])                => `(Term.ofBool $(Lean.quote b))
      | `([StlcFoo| ‹id: $b:term ›])                  => `(Term.var $(Lean.quote b))
      | `([StlcFoo| ‹$t:term› ])                      => `($(Lean.quote t))
      | `([StlcFoo| ite $c then $t else $f])          => `(Term.ite [StlcFoo| $c] [StlcFoo| $t] [StlcFoo| $f])
      | `([StlcFoo| $f $x])                           => `(Term.app [StlcFoo| $f] [StlcFoo| $x])
      | `([StlcFoo| λ $id : $ty:stlc_ty . $b])        => `(Term.abs $(Lean.quote (toString id.getId)) [StlcTy| $ty] [StlcFoo| $b])
      | `([StlcFoo| λ ‹$id:term› : $ty:stlc_ty . $b]) => `(Term.abs $(Lean.quote id) [StlcTy| $ty] [StlcFoo| $b])
      | `([StlcFoo| ( $c:stlc_foo )])                 => `([StlcFoo| $c])

    inductive Value: Term → Prop where
      | true: Value .true
      | false: Value .false
      | abs {id: String} {ty: Ty} {b: Term}: Value [StlcFoo| λ ‹id›: ‹ty›. ‹b›]

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
      | .foo => .foo
      | .ite c t f => .ite (subst id s c) (subst id s t) (subst id s f)

    scoped notation "[" id "↦" s "]" t => Term.subst id s t

    inductive Subst (id: String) (s: Term): Term → Term → Prop where

    namespace Term
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
    end Term

    namespace Tactic
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := by sorry
    end Tactic

    namespace Blended
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
    end Blended

    inductive Eval₁: Term → Term → Prop where
      | appL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [StlcFoo| ‹t₁› ‹t₃›] [StlcFoo| ‹t₂› ‹t₃›]
      | appR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [StlcFoo| ‹v₁› ‹t₁›] [StlcFoo| ‹v₁› ‹t₂›]
      | appAbs {id: String} {ty: Ty} {b v: Term} (h₁: Value v): Eval₁ [StlcFoo| (λ ‹id›: ‹ty›. ‹b›) ‹v›] ([id ↦ v] [StlcFoo| ‹b›])
      | iteTrue {t f: Term}: Eval₁ [StlcFoo| ite tru then ‹t› else ‹f›] [StlcFoo| ‹t›]
      | iteFalse {t f: Term}: Eval₁ [StlcFoo| ite fls then ‹t› else ‹f›] [StlcFoo| ‹f›]
      | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [StlcFoo| ite ‹c₁› then ‹t› else ‹f›] [StlcFoo| ite ‹c₂› then ‹t› else ‹f›]
      | fooAbs {id: String} {t: Term} {ty: Ty}: Eval₁ [StlcFoo| λ ‹id›: ‹ty›. ‹t›] [StlcFoo| foo]
      | foo: Eval₁ [StlcFoo| foo] [StlcFoo| tru]

    scoped infix:50 "⟶" => Eval₁
    scoped infix:50 "⇓" => SmallStep.MultiStep Eval₁

    def Context: Type := PartialMap Ty
    def Context.empty: PartialMap Ty := PartialMap.empty

    scoped notation "●" => Context.empty

    inductive HasType: Context → Term → Ty → Prop where
      | var {Γ: Context} {id: String} {ty: Ty} (h₁: Γ id = .some ty): HasType Γ [StlcFoo| ‹id:id›] ty
      | abs {Γ: Context} {id: String} {ty₁ ty₂: Ty} {b: Term} (h₁: HasType (Γ.update id ty₁) b ty₁): HasType Γ [StlcFoo| λ ‹id›: ‹ty₁›. ‹b›] [StlcTy| ‹ty₁› → ‹ty₂›]
      | app {Γ: Context} {f x: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ f [StlcTy| ‹ty₁› → ‹ty₂›]) (h₂: HasType Γ x ty₁): HasType Γ [StlcFoo| ‹f› ‹x›] ty₂
      | true {Γ: Context}: HasType Γ .true .bool
      | false {Γ: Context}: HasType Γ .false .bool
      | ite {Γ: Context} {c t f: Term} {ty: Ty} (h₁: HasType Γ c .bool) (h₂: HasType Γ t ty) (h₃: HasType Γ f ty): HasType Γ [StlcFoo| ite ‹c› then ‹t› else ‹f›] ty

    scoped notation ctx "⊢" t ":" ty => HasType ctx t ty
  end Variation₂

  namespace Variation₃
    inductive Eval₁: Term → Term → Prop where
      | appR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Stlc| ‹v₁› ‹t₁›] [Stlc| ‹v₁› ‹t₂›]
      | appAbs {id: String} {ty: Ty} {b v: Term} (h₁: Value v): Eval₁ [Stlc| (λ ‹id›: ‹ty›. ‹b›) ‹v›] ([id ↦ v] [Stlc| ‹b›])
      | iteTrue {t f: Term}: Eval₁ [Stlc| ite tru then ‹t› else ‹f›] [Stlc| ‹t›]
      | iteFalse {t f: Term}: Eval₁ [Stlc| ite fls then ‹t› else ‹f›] [Stlc| ‹f›]
      | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [Stlc| ite ‹c₁› then ‹t› else ‹f›] [Stlc| ite ‹c₂› then ‹t› else ‹f›]

    scoped infix:50 "⟶" => Eval₁
    scoped infix:50 "⇓" => SmallStep.MultiStep Eval₁
  end Variation₃

  namespace Variation₄
    inductive Eval₁: Term → Term → Prop where
      | appL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Stlc| ‹t₁› ‹t₃›] [Stlc| ‹t₂› ‹t₃›]
      | appR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Stlc| ‹v₁› ‹t₁›] [Stlc| ‹v₁› ‹t₂›]
      | appAbs {id: String} {ty: Ty} {b v: Term} (h₁: Value v): Eval₁ [Stlc| (λ ‹id›: ‹ty›. ‹b›) ‹v›] ([id ↦ v] [Stlc| ‹b›])
      | iteTrue {t f: Term}: Eval₁ [Stlc| ite tru then ‹t› else ‹f›] [Stlc| ‹t›]
      | iteFalse {t f: Term}: Eval₁ [Stlc| ite fls then ‹t› else ‹f›] [Stlc| ‹f›]
      | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [Stlc| ite ‹c₁› then ‹t› else ‹f›] [Stlc| ite ‹c₂› then ‹t› else ‹f›]
      | funnyIfTrue {t f: Term}: Eval₁ [Stlc| ite tru then ‹t› else ‹f›] [Stlc| tru]

    scoped infix:50 "⟶" => Eval₁
    scoped infix:50 "⇓" => SmallStep.MultiStep Eval₁
  end Variation₄

  namespace Variation₅
    inductive HasType: Context → Term → Ty → Prop where
      | var {Γ: Context} {id: String} {ty: Ty} (h₁: Γ id = .some ty): HasType Γ [Stlc| ‹id:id›] ty
      | abs {Γ: Context} {id: String} {ty₁ ty₂: Ty} {b: Term} (h₁: HasType (Γ.update id ty₁) b ty₁): HasType Γ [Stlc| λ ‹id›: ‹ty₁›. ‹b›] [StlcTy| ‹ty₁› → ‹ty₂›]
      | app {Γ: Context} {f x: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ f [StlcTy| ‹ty₁› → ‹ty₂›]) (h₂: HasType Γ x ty₁): HasType Γ [Stlc| ‹f› ‹x›] ty₂
      | true {Γ: Context}: HasType Γ .true .bool
      | false {Γ: Context}: HasType Γ .false .bool
      | ite {Γ: Context} {c t f: Term} {ty: Ty} (h₁: HasType Γ c .bool) (h₂: HasType Γ t ty) (h₃: HasType Γ f ty): HasType Γ [Stlc| ite ‹c› then ‹t› else ‹f›] ty
      | funnyApp {Γ: Context} {t₁ t₂ t₃: Term} (h₁: HasType Γ t₁ [StlcTy| 𝔹 → 𝔹 → 𝔹]) (h₂: HasType Γ t₂ [StlcTy| 𝔹]): HasType Γ [Stlc| ‹t₁› ‹t₂›] [StlcTy| 𝔹]

    scoped notation ctx "⊢" t ":" ty => HasType ctx t ty
  end Variation₅

  namespace Variation₆
    inductive HasType: Context → Term → Ty → Prop where
      | var {Γ: Context} {id: String} {ty: Ty} (h₁: Γ id = .some ty): HasType Γ [Stlc| ‹id:id›] ty
      | abs {Γ: Context} {id: String} {ty₁ ty₂: Ty} {b: Term} (h₁: HasType (Γ.update id ty₁) b ty₁): HasType Γ [Stlc| λ ‹id›: ‹ty₁›. ‹b›] [StlcTy| ‹ty₁› → ‹ty₂›]
      | app {Γ: Context} {f x: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ f [StlcTy| ‹ty₁› → ‹ty₂›]) (h₂: HasType Γ x ty₁): HasType Γ [Stlc| ‹f› ‹x›] ty₂
      | true {Γ: Context}: HasType Γ .true .bool
      | false {Γ: Context}: HasType Γ .false .bool
      | ite {Γ: Context} {c t f: Term} {ty: Ty} (h₁: HasType Γ c .bool) (h₂: HasType Γ t ty) (h₃: HasType Γ f ty): HasType Γ [Stlc| ite ‹c› then ‹t› else ‹f›] ty
      | funnyApp {Γ: Context} {t₁ t₂ t₃: Term} (h₁: HasType Γ t₁ [StlcTy| 𝔹]) (h₂: HasType Γ t₂ [StlcTy| 𝔹]): HasType Γ [Stlc| ‹t₁› ‹t₂›] [StlcTy| 𝔹]

    scoped notation ctx "⊢" t ":" ty => HasType ctx t ty
  end Variation₆

  namespace Variation₇
    inductive HasType: Context → Term → Ty → Prop where
      | var {Γ: Context} {id: String} {ty: Ty} (h₁: Γ id = .some ty): HasType Γ [Stlc| ‹id:id›] ty
      | abs {Γ: Context} {id: String} {ty₁ ty₂: Ty} {b: Term} (h₁: HasType (Γ.update id ty₁) b ty₁): HasType Γ [Stlc| λ ‹id›: ‹ty₁›. ‹b›] [StlcTy| ‹ty₁› → ‹ty₂›]
      | app {Γ: Context} {f x: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ f [StlcTy| ‹ty₁› → ‹ty₂›]) (h₂: HasType Γ x ty₁): HasType Γ [Stlc| ‹f› ‹x›] ty₂
      | true {Γ: Context}: HasType Γ .true .bool
      | false {Γ: Context}: HasType Γ .false .bool
      | ite {Γ: Context} {c t f: Term} {ty: Ty} (h₁: HasType Γ c .bool) (h₂: HasType Γ t ty) (h₃: HasType Γ f ty): HasType Γ [Stlc| ite ‹c› then ‹t› else ‹f›] ty
      | funnyAbs {Γ: Context} {id: String} {b: Term}: HasType Γ [Stlc| λ ‹id›: 𝔹. ‹b›] [StlcTy| 𝔹]

    scoped notation ctx "⊢" t ":" ty => HasType ctx t ty
  end Variation₇

  namespace Term
    theorem HasType.progress.restatement {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, t₁ ⟶ t₂
      | h => HasType.progress h
    theorem HasType.preservation.restatement {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty)
      | h₁, h₂ => HasType.preservation h₁ h₂

    namespace Variation₁
      open Variation₁

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₁.Eval₁ := sorry
      theorem HasType.progress {t₁: Variation₁.Term} {ty: Ty}: (Variation₁.HasType Variation₁.Context.empty t₁ ty) → Variation₁.Value t ∨ ∃ t₂: Variation₁.Term, Variation₁.Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Variation₁.Term} {ty: Ty}: (Variation₁.HasType Variation₁.Context.empty t₁ ty) → (Variation₁.Eval₁ t₁ t₂) → Variation₁.HasType Variation₁.Context.empty t₂ ty := sorry
    end Variation₁

    namespace Variation₂
      open Variation₂

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₂.Eval₁ := sorry
      theorem HasType.progress {t₁: Variation₂.Term} {ty: Ty}: (Variation₂.HasType Variation₂.Context.empty t₁ ty) → Variation₂.Value t ∨ ∃ t₂: Variation₂.Term, Variation₂.Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Variation₂.Term} {ty: Ty}: (Variation₂.HasType Variation₂.Context.empty t₁ ty) → (Variation₂.Eval₁ t₁ t₂) → Variation₂.HasType Variation₂.Context.empty t₂ ty := sorry
    end Variation₂

    namespace Variation₃
      open Variation₃

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₃.Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, Variation₃.Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (Variation₃.Eval₁ t₁ t₂) → ● ⊢ t₂ : ty := sorry
    end Variation₃

    namespace Variation₄
      open Variation₄

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₄.Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, Variation₄.Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (Variation₄.Eval₁ t₁ t₂) → ● ⊢ t₂ : ty := sorry
    end Variation₄

    namespace Variation₅
      open Variation₅

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₅.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₅.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₅.HasType ● t₂ ty := sorry
    end Variation₅

    namespace Variation₆
      open Variation₆

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₆.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₆.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₆.HasType ● t₂ ty := sorry
    end Variation₆

    namespace Variation₇
      open Variation₇

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₇.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₇.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₇.HasType ● t₂ ty := sorry
    end Variation₇
  end Term

  namespace Tactic
    theorem HasType.progress.restatement {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, t₁ ⟶ t₂ := by sorry
    theorem HasType.preservation.restatement {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := by sorry

    namespace Variation₁
      open Variation₁

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₁.Eval₁ := by sorry
      theorem HasType.progress {t₁: Variation₁.Term} {ty: Ty}: (Variation₁.HasType Variation₁.Context.empty t₁ ty) → Variation₁.Value t ∨ ∃ t₂: Variation₁.Term, Variation₁.Eval₁ t₁ t₂ := by sorry
      theorem HasType.preservation {t₁ t₂: Variation₁.Term} {ty: Ty}: (Variation₁.HasType Variation₁.Context.empty t₁ ty) → (Variation₁.Eval₁ t₁ t₂) → Variation₁.HasType Variation₁.Context.empty t₂ ty := by sorry
    end Variation₁

    namespace Variation₂
      open Variation₂

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₂.Eval₁ := by sorry
      theorem HasType.progress {t₁: Variation₂.Term} {ty: Ty}: (Variation₂.HasType Variation₂.Context.empty t₁ ty) → Variation₂.Value t ∨ ∃ t₂: Variation₂.Term, Variation₂.Eval₁ t₁ t₂ := by sorry
      theorem HasType.preservation {t₁ t₂: Variation₂.Term} {ty: Ty}: (Variation₂.HasType Variation₂.Context.empty t₁ ty) → (Variation₂.Eval₁ t₁ t₂) → Variation₂.HasType Variation₂.Context.empty t₂ ty := by sorry
    end Variation₂

    namespace Variation₃
      open Variation₃

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₃.Eval₁ := by sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, Variation₃.Eval₁ t₁ t₂ := by sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (Variation₃.Eval₁ t₁ t₂) → ● ⊢ t₂ : ty := by sorry
    end Variation₃

    namespace Variation₄
      open Variation₄

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₄.Eval₁ := by sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, Variation₄.Eval₁ t₁ t₂ := by sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (Variation₄.Eval₁ t₁ t₂) → ● ⊢ t₂ : ty := by sorry
    end Variation₄

    namespace Variation₅
      open Variation₅

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := by sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₅.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := by sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₅.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₅.HasType ● t₂ ty := by sorry
    end Variation₅

    namespace Variation₆
      open Variation₆

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := by sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₆.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := by sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₆.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₆.HasType ● t₂ ty := by sorry
    end Variation₆

    namespace Variation₇
      open Variation₇

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := by sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₇.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := by sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₇.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₇.HasType ● t₂ ty := by sorry
    end Variation₇
  end Tactic

  namespace Blended
    theorem HasType.progress.restatement {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
    theorem HasType.preservation.restatement {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := sorry

    namespace Variation₁
      open Variation₁

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₁.Eval₁ := sorry
      theorem HasType.progress {t₁: Variation₁.Term} {ty: Ty}: (Variation₁.HasType Variation₁.Context.empty t₁ ty) → Variation₁.Value t ∨ ∃ t₂: Variation₁.Term, Variation₁.Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Variation₁.Term} {ty: Ty}: (Variation₁.HasType Variation₁.Context.empty t₁ ty) → (Variation₁.Eval₁ t₁ t₂) → Variation₁.HasType Variation₁.Context.empty t₂ ty := sorry
    end Variation₁

    namespace Variation₂
      open Variation₂

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₂.Eval₁ := sorry
      theorem HasType.progress {t₁: Variation₂.Term} {ty: Ty}: (Variation₂.HasType Variation₂.Context.empty t₁ ty) → Variation₂.Value t ∨ ∃ t₂: Variation₂.Term, Variation₂.Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Variation₂.Term} {ty: Ty}: (Variation₂.HasType Variation₂.Context.empty t₁ ty) → (Variation₂.Eval₁ t₁ t₂) → Variation₂.HasType Variation₂.Context.empty t₂ ty := sorry
    end Variation₂

    namespace Variation₃
      open Variation₃

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₃.Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, Variation₃.Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (Variation₃.Eval₁ t₁ t₂) → ● ⊢ t₂ : ty := sorry
    end Variation₃

    namespace Variation₄
      open Variation₄

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Variation₄.Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, Variation₄.Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (Variation₄.Eval₁ t₁ t₂) → ● ⊢ t₂ : ty := sorry
    end Variation₄

    namespace Variation₅
      open Variation₅

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₅.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₅.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₅.HasType ● t₂ ty := sorry
    end Variation₅

    namespace Variation₆
      open Variation₆

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₆.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₆.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₆.HasType ● t₂ ty := sorry
    end Variation₆

    namespace Variation₇
      open Variation₇

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (Variation₇.HasType ● t₁ ty) → Value t ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (Variation₇.HasType ● t₁ ty) → (Variation₃.Eval₁ t₁ t₂) → Variation₇.HasType ● t₂ ty := sorry
    end Variation₇
  end Blended

  namespace StlcArith
    /-
    ### Exercise: STLC with Arithmetic
    -/

    inductive Ty: Type where
      | bool: Ty
      | nat: Ty
      | arrow: Ty → Ty → Ty

    inductive Term: Type where
      | true: Term
      | false: Term
      | var (id: String): Term
      | app (f: Term) (x: Term): Term
      | abs (id: String) (ty: Ty) (b: Term): Term
      | const (n: Nat): Term
      | succ (t: Term): Term
      | pred (t: Term): Term
      | mult (t₁ t₂: Term): Term
      | ite: Term → Term → Term → Term

    @[reducible]
    private def Term.ofBool: Bool → Term
      | .true => Term.true
      | .false => Term.false

    declare_syntax_cat stlc_arith_ty

    syntax:max "𝔹" : stlc_arith_ty
    syntax:max "ℕ" : stlc_arith_ty
    syntax:50 stlc_arith_ty:51 "→" stlc_arith_ty:50 : stlc_arith_ty
    syntax:max "‹" term "›" : stlc_arith_ty

    syntax "(" stlc_arith_ty ")" : stlc_arith_ty

    syntax "[StlcArithTy| " stlc_arith_ty "]" : term

    macro_rules
      | `([StlcArithTy| 𝔹])         => `(Ty.bool)
      | `([StlcArithTy| ℕ])         => `(Ty.nat)
      | `([StlcArithTy| ‹$t:term›]) => `($(Lean.quote t))
      | `([StlcArithTy| $t₁ → $t₂]) => `(Ty.arrow [StlcArithTy| $t₁] [StlcArithTy| $t₂])
      | `([StlcArithTy| ( $ty ) ])  => `([StlcArithTy| $ty])

    declare_syntax_cat stlc_arith

    syntax:max "tru" : stlc_arith
    syntax:max "fls" : stlc_arith
    syntax:max num : stlc_arith
    syntax:max ident : stlc_arith

    syntax:max "‹bool:" term "›" : stlc_arith
    syntax:max "‹nat:" term "›" : stlc_arith
    syntax:max "‹id:" term "›" : stlc_arith
    syntax:max "‹" term "›" : stlc_arith

    syntax:80 "pred" stlc_arith:80 : stlc_arith
    syntax:80 "succ" stlc_arith:80 : stlc_arith
    syntax:70 stlc_arith:70 "×" stlc_arith:71 : stlc_arith
    syntax:50 "ite" stlc_arith "then" stlc_arith "else" stlc_arith : stlc_arith

    syntax:50 "λ" ident ":" stlc_arith_ty "." stlc_arith : stlc_arith
    syntax:50 "λ" "‹" term "›" ":" stlc_arith_ty "." stlc_arith : stlc_arith
    syntax:50 stlc_arith:50 stlc_arith:51 : stlc_arith

    syntax "(" stlc_arith ")" : stlc_arith

    syntax "[StlcArith|" stlc_arith "]" : term

    macro_rules
      | `([StlcArith| tru])                                   => `(Term.true)
      | `([StlcArith| fls])                                   => `(Term.false)
      | `([StlcArith| $n:num])                                => `(Term.const $n)
      | `([StlcArith| $id:ident])                             => `(Term.var $(Lean.quote (toString id.getId)))
      | `([StlcArith| ‹bool: $b:term ›])                      => `(Term.ofBool $(Lean.quote b))
      | `([StlcArith| ‹nat: $n:term ›])                       => `(Term.const $(Lean.quote n))
      | `([StlcArith| ‹id: $b:term ›])                        => `(Term.var $(Lean.quote b))
      | `([StlcArith| ‹$t:term› ])                            => `($(Lean.quote t))
      | `([StlcArith| pred $t])                               => `(Term.pred [StlcArith| $t])
      | `([StlcArith| succ $t])                               => `(Term.succ [StlcArith| $t])
      | `([StlcArith| $t₁ × $t₂])                             => `(Term.mult [StlcArith| $t₁] [StlcArith| $t₂])
      | `([StlcArith| ite $c then $t else $f])                => `(Term.ite [StlcArith| $c] [StlcArith| $t] [StlcArith| $f])
      | `([StlcArith| $f $x])                                 => `(Term.app [StlcArith| $f] [StlcArith| $x])
      | `([StlcArith| λ $id : $ty:stlc_arith_ty . $b])        => `(Term.abs $(Lean.quote (toString id.getId)) [StlcArithTy| $ty] [StlcArith| $b])
      | `([StlcArith| λ ‹$id:term› : $ty:stlc_arith_ty . $b]) => `(Term.abs $(Lean.quote id) [StlcArithTy| $ty] [StlcArith| $b])
      | `([StlcArith| ( $c:stlc_arith )])                     => `([StlcArith| $c])

    inductive Value: Term → Prop where
      | true: Value .true
      | false: Value .false
      | const {n: Nat}: Value (.const n)
      | abs {id: String} {ty: Ty} {b: Term}: Value [StlcArith| λ ‹id›: ‹ty›. ‹b›]

    def Term.subst (id: String) (s: Term): Term → Term
      | .true => .true
      | .false => .false
      | .const n => .const n
      | .var v => if id = v then s else .var v
      | .abs v ty b => if id = v then .abs v ty b else .abs v ty (subst id s b)
      | .app f x => .app (subst id s f) (subst id s x)
      | .pred t => .pred (subst id s t)
      | .succ t => .succ (subst id s t)
      | .mult t₁ t₂ => .mult (subst id s t₁) (subst id s t₂)
      | .ite c t f => .ite (subst id s c) (subst id s t) (subst id s f)

    scoped notation "[" id "↦" s "]" t => Term.subst id s t

    inductive Subst (id: String) (s: Term): Term → Term → Prop where

    namespace Term
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
    end Term

    namespace Tactic
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := by sorry
    end Tactic

    namespace Blended
      theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
    end Blended

    inductive Eval₁: Term → Term → Prop where
      | appL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [StlcArith| ‹t₁› ‹t₃›] [StlcArith| ‹t₂› ‹t₃›]
      | appR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [StlcArith| ‹v₁› ‹t₁›] [StlcArith| ‹v₁› ‹t₂›]
      | appAbs {id: String} {ty: Ty} {b v: Term} (h₁: Value v): Eval₁ [StlcArith| (λ ‹id›: ‹ty›. ‹b›) ‹v›] ([id ↦ v] [StlcArith| ‹b›])
      | succ {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [StlcArith| pred ‹t₁›] [StlcArith| pred ‹t₂›]
      | predZero: Eval₁ [StlcArith| pred 0] [StlcArith| 0]
      | predSucc {v: Term} (h₁: Value v): Eval₁ [StlcArith| pred succ ‹v›] [StlcArith| ‹v›]
      | pred {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [StlcArith| pred ‹t₁›] [StlcArith| pred ‹t₂›]
      | multL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [StlcArith| ‹t₁› × ‹t₃›] [StlcArith| ‹t₂› × ‹t₃›]
      | multR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [StlcArith| ‹v₁› × ‹t₁›] [StlcArith| ‹v₁› × ‹v₂›]
      | mult {n₁ n₂: Nat}: Eval₁ [StlcArith| ‹nat:n₁› × ‹nat:n₂›] [StlcArith| ‹nat:n₁ × n₂›]
      | iteTrue {t f: Term}: Eval₁ [StlcArith| ite tru then ‹t› else ‹f›] [StlcArith| ‹t›]
      | iteFalse {t f: Term}: Eval₁ [StlcArith| ite fls then ‹t› else ‹f›] [StlcArith| ‹f›]
      | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [StlcArith| ite ‹c₁› then ‹t› else ‹f›] [StlcArith| ite ‹c₂› then ‹t› else ‹f›]

    scoped infix:50 "⟶" => Eval₁
    scoped infix:50 "⇓" => SmallStep.MultiStep Eval₁

    namespace Term
      example: ∃ t: Term, [StlcArith| λ x: ℕ. λ y: ℕ. x × y] ⇓ t := sorry
    end Term

    namespace Tactic
      example: ∃ t: Term, [StlcArith| λ x: ℕ. λ y: ℕ. x × y] ⇓ t := by sorry
    end Tactic

    namespace Blended
      example: ∃ t: Term, [StlcArith| λ x: ℕ. λ y: ℕ. x × y] ⇓ t := sorry
    end Blended

    open SoftwareFoundations.LogicalFoundations.Maps

    def Context: Type := PartialMap Ty
    def Context.empty: PartialMap Ty := PartialMap.empty

    scoped notation "●" => Context.empty

    inductive HasType: Context → Term → Ty → Prop where
      | true {Γ: Context}: HasType Γ .true .bool
      | false {Γ: Context}: HasType Γ .false .bool
      | const {Γ: Context} {n: Nat}: HasType Γ (.const n) .nat
      | var {Γ: Context} {id: String} {ty: Ty} (h₁: Γ id = .some ty): HasType Γ [StlcArith| ‹id:id›] ty
      | abs {Γ: Context} {id: String} {ty₁ ty₂: Ty} {b: Term} (h₁: HasType (Γ.update id ty₁) b ty₁): HasType Γ [StlcArith| λ ‹id›: ‹ty₁›. ‹b›] [StlcArithTy| ‹ty₁› → ‹ty₂›]
      | app {Γ: Context} {f x: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ f [StlcArithTy| ‹ty₁› → ‹ty₂›]) (h₂: HasType Γ x ty₁): HasType Γ [StlcArith| ‹f› ‹x›] ty₂
      | succ {Γ: Context} {t: Term} (h₁: HasType Γ t .nat): HasType Γ [StlcArith| succ ‹t›] .nat
      | pred {Γ: Context} {t: Term} (h₁: HasType Γ t .nat): HasType Γ [StlcArith| pred ‹t›] .nat
      | mult {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ .nat) (h₂: HasType Γ t₂ .nat): HasType Γ [StlcArith| ‹t₁› × ‹t₂›] .nat
      | ite {Γ: Context} {c t f: Term} {ty: Ty} (h₁: HasType Γ c .bool) (h₂: HasType Γ t ty) (h₃: HasType Γ f ty): HasType Γ [StlcArith| ite ‹c› then ‹t› else ‹f›] ty

    scoped notation ctx "⊢" t ":" ty => HasType ctx t ty

    namespace Term
      example: (● ⊢ [StlcArith| (λ x: ℕ. λ y: ℕ. x × y) 3 2] : [StlcArithTy| ℕ]) := sorry
    end Term

    namespace Tactic
      example: (● ⊢ [StlcArith| (λ x: ℕ. λ y: ℕ. x × y) 3 2] : [StlcArithTy| ℕ]) := by sorry
    end Tactic

    namespace Blended
      example: (● ⊢ [StlcArith| (λ x: ℕ. λ y: ℕ. x × y) 3 2] : [StlcArithTy| ℕ]) := sorry
    end Blended

    /-
    ### The Technical Theorems
    -/

    namespace Term
      theorem Context.weakening {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: Γ₁.includedIn Γ₂ → (Γ₁ ⊢ t : ty) → Γ₂ ⊢ t : ty := sorry
      theorem Context.weakening.empty {Γ: Context} {t: Term} {ty: Ty}: (● ⊢ t : ty) → Γ ⊢ t : ty := sorry

      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := sorry
    end Term

    namespace Tactic
      theorem Context.weakening {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: Γ₁.includedIn Γ₂ → (Γ₁ ⊢ t : ty) → Γ₂ ⊢ t : ty := by sorry
      theorem Context.weakening.empty {Γ: Context} {t: Term} {ty: Ty}: (● ⊢ t : ty) → Γ ⊢ t : ty := by sorry

      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := by sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := by sorry
    end Tactic

    namespace Blended
      theorem Context.weakening {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: Γ₁.includedIn Γ₂ → (Γ₁ ⊢ t : ty) → Γ₂ ⊢ t : ty := sorry
      theorem Context.weakening.empty {Γ: Context} {t: Term} {ty: Ty}: (● ⊢ t : ty) → Γ ⊢ t : ty := sorry

      theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := sorry
    end Blended
  end StlcArith
end SoftwareFoundations.ProgrammingLanguageFoundations.Stlc
