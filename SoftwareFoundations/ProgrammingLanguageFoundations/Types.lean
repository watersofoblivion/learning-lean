/-
# Type Systems
-/

import SoftwareFoundations.LogicalFoundations.Maps
import SoftwareFoundations.ProgrammingLanguageFoundations.SmallStep

namespace SoftwareFoundations.ProgrammingLanguageFoundations.Types
  /-
  ## Typed Arithmetic Expressions
  -/

  /-
  ### Syntax
  -/

  inductive Term: Type where
    | true: Term
    | false: Term
    | zero: Term
    | ite: Term → Term → Term → Term
    | succ: Term → Term
    | pred: Term → Term
    | isZero: Term → Term

  declare_syntax_cat ty_arith

  syntax:max "tru" : ty_arith
  syntax:max "fls" : ty_arith
  syntax:max num : ty_arith

  syntax:max "‹nat:" term "›" : ty_arith
  syntax:max "‹bool:" term "›" : ty_arith
  syntax:max "‹" term "›" : ty_arith

  syntax:50 "ite" "(" ty_arith ")" "{" ty_arith "}" "else" "{" ty_arith "}" : ty_arith
  syntax:60 "succ" ty_arith : ty_arith
  syntax:60 "pred" ty_arith : ty_arith
  syntax:60 "isZero" ty_arith : ty_arith

  syntax "(" ty_arith ")" : ty_arith

  syntax "[TyArith|" ty_arith "]" : term

  @[reducible]
  private def Term.ofBool: Bool → Term
    | .true => Term.true
    | .false => Term.false

  @[reducible]
  private def Term.ofNat: Nat → Term
    | .zero => Term.zero
    | .succ n => Term.succ (Term.ofNat n)

  macro_rules
    | `([TyArith| tru])                           => `(Term.true)
    | `([TyArith| fls])                           => `(Term.false)
    | `([TyArith| ‹bool: $b:term ›])              => `(Term.ofBool $(Lean.quote b))
    | `([TyArith| ‹nat: $n:term ›])               => `(Term.ofNat $(Lean.quote n))
    | `([TyArith| $n:num])                        => `(Term.ofNat $n)
    | `([TyArith| ‹$t:term› ])                    => `($(Lean.quote t))
    | `([TyArith| ite ( $c ) { $t } else { $f }]) => `(Term.ite [TyArith| $c] [TyArith| $t] [TyArith| $f])
    | `([TyArith| succ $n])                       => `(Term.succ [TyArith| $n])
    | `([TyArith| pred $n])                       => `(Term.pred [TyArith| $n])
    | `([TyArith| isZero $n])                     => `(Term.isZero [TyArith| $n])
    | `([TyArith| ( $c )])                        => `([TyArith| $c])

  example: [TyArith| tru] = Term.true := rfl
  example: [TyArith| fls] = Term.false := rfl
  example: [TyArith| ‹bool:true›] = Term.true := rfl
  example: [TyArith| ‹bool:false›] = Term.false := rfl

  example: [TyArith| 0] = Term.zero := rfl
  example: [TyArith| succ 0] = Term.succ .zero := rfl
  example: [TyArith| succ succ 0] = Term.succ (.succ .zero) := rfl
  example: [TyArith| succ pred succ 0] = Term.succ (.pred (.succ .zero)) := rfl
  example: [TyArith| isZero succ pred succ 0] = Term.isZero (.succ (.pred (.succ .zero))) := rfl

  example: [TyArith| ite (isZero succ 0) { tru } else { fls }] = Term.ite (.isZero (.succ .zero)) .true .false := rfl

  example: [TyArith| 0] = Term.zero := rfl
  example: [TyArith| 1] = Term.succ .zero := rfl
  example: [TyArith| 2] = Term.succ (.succ .zero) := rfl
  example: [TyArith| ‹nat:0›] = Term.zero := rfl
  example: [TyArith| ‹nat:1›] = Term.succ .zero := rfl
  example: [TyArith| ‹nat:2›] = Term.succ (.succ .zero) := rfl
  example: [TyArith| succ pred 1] = Term.succ (.pred (.succ .zero)) := rfl
  example: [TyArith| isZero succ pred 1] = Term.isZero (.succ (.pred (.succ .zero))) := rfl

  inductive BoolValue: Term → Prop where
    | true: BoolValue [TyArith| tru]
    | false: BoolValue [TyArith| fls]

  inductive NatValue: Term → Prop where
    | zero: NatValue [TyArith| 0]
    | succ {t: Term} (h: NatValue [TyArith| ‹t›]): NatValue [TyArith| succ ‹t›]

  def Value (t: Term): Prop := BoolValue t ∨ NatValue t

  /-
  ### Operational Semantics
  -/

  inductive Eval₁: Term → Term → Prop where
    | iteTrue {t f: Term}: Eval₁ [TyArith| ite (tru) { ‹t› } else { ‹f› }] [TyArith| ‹t›]
    | iteFalse {t f: Term}: Eval₁ [TyArith| ite (fls) { ‹t› } else { ‹f› }] [TyArith| ‹f›]
    | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [TyArith| ite (‹c₁›) { ‹t› } else { ‹f› }] [TyArith| ite (‹c₂›) { ‹t› } else { ‹f› }]
    | succ {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| succ ‹t₁›] [TyArith| succ ‹t₂›]
    | predZero: Eval₁ [TyArith| pred 0] [TyArith| 0]
    | predSucc {v: Term} (h₁: NatValue v): Eval₁ [TyArith| pred succ ‹v›] [TyArith| ‹v›]
    | pred {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| pred ‹t₁›] [TyArith| pred ‹t₂›]
    | isZeroZero: Eval₁ [TyArith| isZero 0] [TyArith| tru]
    | isZeroSucc {v: Term} (h₁: NatValue v): Eval₁ [TyArith| isZero succ ‹v›] [TyArith| fls]
    | isZero {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| isZero ‹t₁›] [TyArith| isZero ‹t₂›]

  infix:50 "⟶" => Eval₁

  instance: Trans Eval₁ Eval₁ Eval₁ where
    trans hxy hyz := sorry

  /-
  ### Normal Forms and Values
  -/

  @[reducible]
  def Term.normal: Term → Prop := SmallStep.Relation.normal Eval₁

  @[reducible]
  def Term.stuck (t: Term): Prop := t.normal ∧ ¬ Value t

  namespace Term
    example: ∃ t: Term, t.stuck :=
      have w := [TyArith| succ tru]
      have hw: w.normal ∧ ¬ Value w :=
        have hn: (∃ t₂, w ⟶ t₂) → False
          | ⟨w₂, hw₂⟩ => sorry
        have hnv: Value w → False
          | .inl h => sorry
          | .inr h => sorry
        ⟨hn, hnv⟩
      ⟨w, hw⟩

    theorem Value.normal {t: Term}: Value t → t.normal
      | .inl .true, ⟨w, hw⟩  => sorry
      | .inl .false, ⟨w, hw⟩ => sorry
      | .inr .zero, ⟨w, hw⟩  => sorry
      | .inr (.succ hv), ⟨w, hw⟩  =>
        sorry

    theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁
      | _, _, _, .iteTrue,      .iteTrue
      | _, _, _, .iteFalse,     .iteFalse
      | _, _, _, .predZero,     .predZero
      | _, _, _, .predSucc _,   .predSucc _
      | _, _, _, .isZeroZero,   .isZeroZero
      | _, _, _, .isZeroSucc _, .isZeroSucc _ => rfl
      | _, _, _, .ite h₁, .ite h₂ =>
        have ih := deterministic h₁ h₂
        calc Term.ite _ _ _
          _ = .ite _ _ _ := congr (congr (congrArg Term.ite ih) rfl) rfl
      | _, _, _, .succ h₁, .succ h₂ =>
        have ih := deterministic h₁ h₂
        calc Term.succ _
          _ = .succ _ := congrArg Term.succ ih
      | _, _, _, .pred h₁, .pred h₂ =>
        have ih := deterministic h₁ h₂
        calc Term.pred _
          _ = .pred _ := congrArg Term.pred ih
      | _, _, _, .isZero h₁, .isZero h₂ =>
        have ih := deterministic h₁ h₂
        calc Term.isZero _
          _ = .isZero _ := congrArg Term.isZero ih
      | _, _, _, .predSucc hv,      .pred (.succ h)
      | _, _, _, .pred (.succ h),   .predSucc hv
      | _, _, _, .isZeroSucc hv,    .isZero (.succ h)
      | _, _, _, .isZero (.succ h), .isZeroSucc hv =>
        have hvn := Value.normal (.inr hv)
        have hf := hvn ⟨_, h⟩
        False.elim hf
  end Term

  namespace Tactic
    example: ∃ t: Term, t.stuck := by
      exists [TyArith| succ tru]
      · apply And.intro
        · intro
          | .intro w hw => contradiction
        · intro
          | .inl _ => contradiction
          | .inr h =>
            cases h with
              | «succ» h => contradiction

    theorem Value.normal {t: Term} (h: Value t): t.normal := by
      cases h with
        | inl h => cases h <;> (intro
                                | .intro w hw => contradiction)
        | inr h =>
          cases h with
            | zero =>
              intro
              | .intro w hw => contradiction
            | «succ» _ => sorry

    theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := by
      intro _ _ _ h₁ h₂
      induction h₁ <;> cases h₂ <;> try (first | rfl
                                               | contradiction)
      case ite.ite       _ h₁ _ h₂ _
         | succ.succ     _ h₁ _ h₂ _
         | pred.pred     _ h₁ _ h₂ _
         | isZero.isZero _ h₁ _ h₂ _ => rw [deterministic h₁ h₂]
      case predSucc.pred     _ _ _ hv h₂ ih
         | pred.predSucc     _ _ _ hv h₂ ih
         | isZeroSucc.isZero _ _ _ hv h₂ ih
         | isZero.isZeroSucc _ _ _ hv h₂ ih => sorry
  end Tactic

  namespace Blended
    example: ∃ t: Term, t.stuck := sorry

    theorem Value.normal {t: Term}: Value t → t.normal
      | .inl .true, ⟨w, hw⟩
      | .inl .false, ⟨w, hw⟩
      | .inr .zero, ⟨w, hw⟩  => by contradiction
      | .inr (.succ hv), ⟨w, hw⟩ => by
        have ih := normal (.inr hv)
        sorry

    theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁
      | _, _, _, .iteTrue,      .iteTrue
      | _, _, _, .iteFalse,     .iteFalse
      | _, _, _, .predZero,     .predZero
      | _, _, _, .predSucc _,   .predSucc _
      | _, _, _, .isZeroZero,   .isZeroZero
      | _, _, _, .isZeroSucc _, .isZeroSucc _ => by rfl
      | _, _, _, .ite h₁,    .ite h₂
      | _, _, _, .succ h₁,   .succ h₂
      | _, _, _, .pred h₁,   .pred h₂
      | _, _, _, .isZero h₁, .isZero h₂ => by rw [deterministic h₁ h₂]
      | _, _, _, .predSucc hv,      .pred (.succ h)
      | _, _, _, .pred (.succ h),   .predSucc hv
      | _, _, _, .isZeroSucc hv,    .isZero (.succ h)
      | _, _, _, .isZero (.succ h), .isZeroSucc hv =>
        have hvn := Value.normal (.inr hv) ⟨_, h⟩
        by contradiction
  end Blended

  /-
  ### Typing
  -/

  inductive Ty: Type where
    | bool: Ty
    | nat: Ty

  inductive HasType: Term → Ty → Prop where
    | true: HasType [TyArith| tru] .bool
    | false: HasType [TyArith| fls] .bool
    | ite {c t f: Term} {ty: Ty} (h₁: HasType c .bool) (h₂: HasType t ty) (h₂: HasType f ty): HasType [TyArith| ite (‹c›) { ‹t› } else { ‹f› }] ty
    | zero: HasType [TyArith| 0] .nat
    | succ {t: Term} (h₁: HasType t .nat): HasType [TyArith| succ ‹t›] .nat
    | pred {t: Term} (h₁: HasType t .nat): HasType [TyArith| pred ‹t›] .nat
    | isZero {t: Term} (h₁: HasType t .nat): HasType [TyArith| isZero ‹t›] .bool

  notation "⊢" t ":" ty => HasType t ty

  namespace Term
    example: ⊢ [TyArith| ite (fls) { 0 } else { succ 0 }] : .nat :=
      .ite .false .zero (.succ .zero)

    example: ¬ ⊢ [TyArith| ite (fls) { 0 } else { tru }] : .bool
      | hht => sorry

    example {t: Term}: (⊢ [TyArith| succ ‹t›] : .nat) → ⊢ t : .nat
      | .succ h => h
  end Term

  namespace Tactic
    example: ⊢ [TyArith| ite (fls) { 0 } else { succ 0 }] : .nat := by
      apply HasType.ite
      · exact HasType.false
      · exact HasType.zero
      · apply HasType.succ
        · exact HasType.zero

    example: ¬ ⊢ [TyArith| ite (fls) { 0 } else { tru }] : .bool := by
      intro _
      contradiction

    example {t: Term}: (⊢ [TyArith| succ ‹t›] : .nat) → ⊢ t : .nat := by
      intro
      | .succ h => exact h
  end Tactic

  namespace Blended
    example: ⊢ [TyArith| ite (fls) { 0 } else { succ 0 }] : .nat :=
      .ite .false .zero (.succ .zero)

    example: ¬ ⊢ [TyArith| ite (fls) { 0 } else { tru }] : .bool
      | _ => by contradiction

    example {t: Term}: (⊢ [TyArith| succ ‹t›] : .nat) → ⊢ t : .nat
      | .succ h => h
  end Blended

  /-
  #### Canonical Forms
  -/

  namespace Term
    theorem Ty.canonical.bool {t: Term}: (⊢ t : .bool) → Value t → BoolValue t
      | .true, .inl h => h
      | .false, .inl h => h

    theorem Ty.canonical.nat {t: Term}: (⊢ t : .nat) → Value t → NatValue t
      | .zero, .inr h => h
      | .succ _, .inr h => h
  end Term

  namespace Tactic
    theorem Ty.canonical.bool {t: Term} (h₁: ⊢ t : .bool) (h₂: Value t): BoolValue t := by
      cases h₁ <;> cases h₂ <;> try contradiction
      case true.inl h => exact h
      case false.inl h => exact h

    theorem Ty.canonical.nat {t: Term} (h₁: ⊢ t : .nat) (h₂: Value t): NatValue t := by
      cases h₁ <;> cases h₂ <;> try contradiction
      case zero.inr h => exact h
      case succ.inr h => exact h
  end Tactic

  namespace Blended
    theorem Ty.canonical.bool {t: Term}: (⊢ t : .bool) → Value t → BoolValue t
      | .true, .inl h => h
      | .false, .inl h => h

    theorem Ty.canonical.nat {t: Term}: (⊢ t : .nat) → Value t → NatValue t
      | .zero, .inr h => h
      | .succ _, .inr h => h
  end Blended

  /-
  ### Progress
  -/

  namespace Term
    theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂
      | .true  => .inl (.inl .true)
      | .false => .inl (.inl .false)
      | .zero  => .inl (.inr .zero)
      | .ite .true  _ _ => .inr ⟨_, .iteTrue⟩
      | .ite .false _ _ => .inr ⟨_, .iteFalse⟩
      | .ite h₁ _ _ =>
        match progress h₁ with
          | .inl (.inl .true)  => .inr ⟨_, .iteTrue⟩
          | .inl (.inl .false) => .inr ⟨_, .iteFalse⟩
          | .inl (.inr hv)     => sorry
          | .inr ⟨_, hw⟩       => .inr ⟨_, .ite hw⟩
      | .succ h₁ =>
        match progress h₁ with
          | .inl (.inl hv) => sorry
          | .inl (.inr hv) => .inl (.inr (.succ hv))
          | .inr ⟨_, hw⟩   => .inr ⟨_, .succ hw⟩
      | .pred h₁ =>
        match progress h₁ with
          | .inl (.inl hv)        => sorry
          | .inl (.inr .zero)     => .inr ⟨_, .predZero⟩
          | .inl (.inr (.succ h)) => .inr ⟨_, .predSucc h⟩
          | .inr ⟨_, hw⟩          => .inr ⟨_, .pred hw⟩
      | .isZero h₁ =>
        match progress h₁ with
          | .inl (.inl hv)        => sorry
          | .inl (.inr .zero)     => .inr ⟨_, .isZeroZero⟩
          | .inl (.inr (.succ h)) => .inr ⟨_, .isZeroSucc h⟩
          | .inr ⟨_, hw⟩          => .inr ⟨_, .isZero hw⟩
  end Term

  namespace Tactic
    theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := by
      intro hht
      induction hht with
        | true =>
          apply Or.inl
          · apply Or.inl
            · apply BoolValue.true
        | false =>
          apply Or.inl
          · apply Or.inl
            · apply BoolValue.false
        | zero =>
          apply Or.inl
          · apply Or.inr
            · apply NatValue.zero
        | «ite» c t f ihc iht ihf =>
          cases c with
            | true =>
              apply Or.inr
              · apply Exists.intro
                · apply Eval₁.iteTrue
            | false =>
              apply Or.inr
              · apply Exists.intro
                · apply Eval₁.iteFalse
            | «ite» _ _ _ => sorry
            | «isZero» _ => sorry
        | «succ» h ih =>
          cases ih with
            | inl h =>
              cases h with
                | inl h => sorry
                | inr h =>
                  apply Or.inl
                  · apply Or.inr
                    · apply NatValue.succ h
            | inr h =>
              cases h with
                | intro w hw =>
                  apply Or.inr
                  · apply Exists.intro
                    apply Eval₁.succ
                    · exact hw
        | «pred» _ ih =>
          cases ih with
            | inl h =>
              cases h with
                | inl h => sorry
                | inr h =>
                  cases h with
                    | zero =>
                      apply Or.inr
                      · apply Exists.intro
                        · apply Eval₁.predZero
                    | «succ» _ =>
                      apply Or.inr
                      · apply Exists.intro
                        · apply Eval₁.predSucc
                          · assumption
            | inr h =>
              cases h with
                | intro _ hw =>
                  apply Or.inr
                  · apply Exists.intro
                    · apply Eval₁.pred
                      · exact hw
        | «isZero» _ ih =>
          cases ih with
            | inl h =>
              cases h with
                | inl h => sorry
                | inr h =>
                  cases h with
                    | zero =>
                      apply Or.inr
                      · apply Exists.intro
                        · apply Eval₁.isZeroZero
                    | «succ» _ =>
                      apply Or.inr
                      · apply Exists.intro
                        · apply Eval₁.isZeroSucc
                          · assumption
            | inr h =>
              cases h with
                | intro _ hw =>
                  apply Or.inr
                  . apply Exists.intro
                    · apply Eval₁.isZero
                      · exact hw
  end Tactic

  namespace Blended
    theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂
      | .true  => .inl (.inl .true)
      | .false => .inl (.inl .false)
      | .zero  => .inl (.inr .zero)
      | .ite .true  _ _ => .inr ⟨_, .iteTrue⟩
      | .ite .false _ _ => .inr ⟨_, .iteFalse⟩
      | .ite h₁ _ _ =>
        match progress h₁ with
          | .inl (.inl .true)  => .inr ⟨_, .iteTrue⟩
          | .inl (.inl .false) => .inr ⟨_, .iteFalse⟩
          | .inl (.inr hv)     => sorry
          | .inr ⟨w, hw⟩       => .inr ⟨_, .ite hw⟩
      | .succ h₁ =>
        match progress h₁ with
          | .inl (.inl hv) => sorry
          | .inl (.inr hv) => .inl (.inr (.succ hv))
          | .inr ⟨w, hw⟩   => .inr ⟨_, .succ hw⟩
      | .pred h₁ =>
        match progress h₁ with
          | .inl (.inl hv)        => sorry
          | .inl (.inr .zero)     => .inr ⟨_, .predZero⟩
          | .inl (.inr (.succ h)) => .inr ⟨_, .predSucc h⟩
          | .inr ⟨w, hw⟩          => .inr ⟨_, .pred hw⟩
      | .isZero h₁ =>
        match progress h₁ with
          | .inl (.inl hv)        => sorry
          | .inl (.inr .zero)     => .inr ⟨_, .isZeroZero⟩
          | .inl (.inr (.succ h)) => .inr ⟨_, .isZeroSucc h⟩
          | .inr ⟨w, hw⟩          => .inr ⟨_, .isZero hw⟩
  end Blended

  /-
  ### Type Preservation
  -/

  namespace Term
    theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty
      | .true, h => contradiction (.inl .true) h
      | .false, h => contradiction (.inl .false) h
      | .zero, h => contradiction (.inr .zero) h
      | .ite .true h₂ _, .iteTrue => h₂
      | .ite .false _ h₃, .iteFalse => h₃
      | .ite h₁ h₂ h₃, .ite h    =>
        have ih := preservation h₁ h
        .ite ih h₂ h₃
      | .succ h₁, .succ h =>
        have ih := preservation h₁ h
        .succ ih
      | .pred .zero, .predZero => .zero
      | .pred (.succ h), .predSucc _ => h
      | .pred h₁, .pred h =>
        have ih := preservation h₁ h
        .pred ih
      | .isZero .zero, .isZeroZero => .true
      | .isZero (.succ n), .isZeroSucc _ => .false
      | .isZero h₁, .isZero h =>
        have ih := preservation h₁ h
        .isZero ih
      where
        contradiction {α} {t₁ t₂: Term} (hv: Value t₁) (h: t₁ ⟶ t₂): α :=
          have hvn := Value.normal hv
          have hf := hvn ⟨_, h⟩
          False.elim hf
  end Term

  namespace Tactic
    theorem HasType.preservation {t₁ t₂: Term} {ty: Ty} (h₁: ⊢ t₁ : ty) (h₂: Eval₁ t₁ t₂): ⊢ t₂ : ty := by
      induction h₁ with
        | true => contradiction
        | false => contradiction
        | zero => contradiction
        | «ite» c t f ihc iht ihf =>
          cases c with
            | true =>
              cases h₂ with
                | iteTrue => exact t
                | «ite» => sorry
            | false =>
              cases h₂ with
                | iteFalse => exact f
                | «ite» => sorry
            | «ite» => sorry
            | «isZero» h => sorry
        | «succ» h ih => sorry
        | «pred» h ih =>
          cases h with
            | zero =>
              cases h₂ with
                | predZero => exact HasType.zero
                | «pred» h => sorry
            | «ite» c t f => sorry
            | «succ» h => sorry
            | «pred» h => sorry
        | «isZero» h ih =>
          cases h with
            | zero =>
              cases h₂ with
                | isZeroZero => exact HasType.true
                | «isZero» => sorry
            | «ite» c t f => sorry
            | «succ» h => sorry
            | «pred» h => sorry

    example {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty := by sorry
  end Tactic

  namespace Blended
    theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty
      | .true, _ => by contradiction
      | .false, _ => by contradiction
      | .zero, _ => by contradiction
      | .ite .true h₂ _, .iteTrue => h₂
      | .ite .false _ h₃, .iteFalse => h₃
      | .ite h₁ h₂ h₃, .ite h =>
        have ih := preservation h₁ h
        .ite ih h₂ h₃
      | .succ h₁, .succ h =>
        have ih := preservation h₁ h
        .succ ih
      | .pred .zero, .predZero => .zero
      | .pred (.succ h), .predSucc _ => h
      | .pred h₁, .pred h =>
        have ih := preservation h₁ h
        .pred ih
      | .isZero .zero, .isZeroZero => .true
      | .isZero (.succ n), .isZeroSucc _ => .false
      | .isZero h₁, .isZero h =>
        have ih := preservation h₁ h
        .isZero ih
  end Blended

  /-
  ### Type Soundness
  -/

  -- def Term.stuck (t: Term): Prop := t.normal ∧ ¬ Value t
  -- def Relation.normal (R: Relation α) (t₁: α): Prop := ¬ ∃ t₂: α, R t₁ t₂

  namespace Term
    theorem HasType.sound {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → SmallStep.MultiStep Eval₁ t₁ t₂ → ¬ t₂.stuck
      | .true, .refl, ⟨_, hnv⟩ => absurd (.inl .true) hnv
      | .false, .refl, ⟨_, hnv⟩ => absurd (.inl .false) hnv
      | .zero, .refl, ⟨_, hnv⟩ => absurd (.inr .zero) hnv
      | .ite .true h₂ _, .step .iteTrue h, hs => sound h₂ h hs
      | .ite .false _ h₃, .step .iteFalse h, hs => sound h₃ h hs
      | .ite h₁ h₂ h₃, h, hs => sorry
      | .succ h₁, h, hs => sorry
      | .pred .zero, .step .predZero h, hs => sound .zero h hs
      | .pred (.succ h₁), .step (.predSucc hv) h, hs => sound h₁ h hs
      | .pred h₁, h, ⟨hn, hnv⟩ => sorry
      | .isZero .zero, .step .isZeroZero h, hs => sound .true h hs
      | .isZero (.succ h₁), .step (.isZeroSucc hv) h, hs => sound .false h hs
      | .isZero h₁, h, ⟨hn, hnv⟩ => sorry
  end Term

  namespace Tactic
    theorem HasType.sound {t₁ t₂: Term} {ty: Ty} (h₁: ⊢ t₁ : ty) (h₂: SmallStep.MultiStep Eval₁ t₁ t₂): ¬ t₂.stuck := by sorry
  end Tactic

  namespace Blended
    theorem HasType.sound {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → SmallStep.MultiStep Eval₁ t₁ t₂ → ¬ t₂.stuck
      | .true, .refl, ⟨_, hnv⟩ =>
        have hv: Value .true := .inl .true
        by contradiction
      | .false, .refl, ⟨_, hnv⟩ =>
        have hv: Value .false := .inl .false
        absurd (.inl .false) hnv
      | .zero, .refl, ⟨_, hnv⟩ =>
        have hv: Value .zero := .inr .zero
        by contradiction
      | .ite .true h₂ _, .step .iteTrue h, hs => sound h₂ h hs
      | .ite .false _ h₃, .step .iteFalse h, hs => sound h₃ h hs
      | .ite h₁ h₂ h₃, h, hs => sorry
      | .succ h₁, h, hs => sorry
      | .pred .zero, .step .predZero h, hs => sound .zero h hs
      | .pred (.succ h₁), .step (.predSucc hv) h, hs => sound h₁ h hs
      | .pred h₁, h, ⟨hn, hnv⟩ => sorry
      | .isZero .zero, .step .isZeroZero h, hs => sound .true h hs
      | .isZero (.succ h₁), .step (.isZeroSucc hv) h, hs => sound .false h hs
      | .isZero h₁, h, ⟨hn, hnv⟩ => sorry
  end Blended

  /-
  ### Additional Exercises
  -/

  namespace Term
    example {t₁ t₂: Term} {ty: Ty}: (Eval₁ t₁ t₂ ∧ (⊢ t₂ : ty) → ⊢ t₁ : ty) ∨ ¬(Eval₁ t₁ t₂ ∧ (⊢ t₂ : ty) → ⊢ t₁ : ty) := sorry

    namespace Variation1
      inductive HasType: Term → Ty → Prop where
        | true: HasType [TyArith| tru] .bool
        | false: HasType [TyArith| fls] .bool
        | ite {c t f: Term} {ty: Ty} (h₁: HasType c .bool) (h₂: HasType t ty) (h₂: HasType f ty): HasType [TyArith| ite (‹c›) { ‹t› } else { ‹f› }] ty
        | zero: HasType [TyArith| 0] .nat
        | succ {t: Term} (h₁: HasType t .nat): HasType [TyArith| succ ‹t›] .nat
        | pred {t: Term} (h₁: HasType t .nat): HasType [TyArith| pred ‹t›] .nat
        | isZero {t: Term} (h₁: HasType t .nat): HasType [TyArith| isZero ‹t›] .bool
        | succBool {t: Term} (h₁: HasType t .bool): HasType [TyArith| succ ‹t›] .bool

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty := sorry
    end Variation1

    namespace Variation2
      inductive Eval₁: Term → Term → Prop where
        | iteTrue {t f: Term}: Eval₁ [TyArith| ite (tru) { ‹t› } else { ‹f› }] [TyArith| ‹t›]
        | iteFalse {t f: Term}: Eval₁ [TyArith| ite (fls) { ‹t› } else { ‹f› }] [TyArith| ‹f›]
        | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [TyArith| ite (‹c₁›) { ‹t› } else { ‹f› }] [TyArith| ite (‹c₂›) { ‹t› } else { ‹f› }]
        | succ {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| succ ‹t₁›] [TyArith| succ ‹t₂›]
        | predZero: Eval₁ [TyArith| pred 0] [TyArith| 0]
        | predSucc {v: Term} (h₁: NatValue v): Eval₁ [TyArith| pred succ ‹v›] [TyArith| ‹v›]
        | pred {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| pred ‹t₁›] [TyArith| pred ‹t₂›]
        | isZeroZero: Eval₁ [TyArith| isZero 0] [TyArith| tru]
        | isZeroSucc {v: Term} (h₁: NatValue v): Eval₁ [TyArith| isZero succ ‹v›] [TyArith| fls]
        | isZero {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| isZero ‹t₁›] [TyArith| isZero ‹t₂›]
        | funny {t f: Term}: Eval₁ [TyArith| ite (tru) { ‹t› } else { ‹f› }] [TyArith| ‹f›]

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty := sorry
    end Variation2

    namespace Variation3
      inductive Eval₁: Term → Term → Prop where
        | iteTrue {t f: Term}: Eval₁ [TyArith| ite (tru) { ‹t› } else { ‹f› }] [TyArith| ‹t›]
        | iteFalse {t f: Term}: Eval₁ [TyArith| ite (fls) { ‹t› } else { ‹f› }] [TyArith| ‹f›]
        | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [TyArith| ite (‹c₁›) { ‹t› } else { ‹f› }] [TyArith| ite (‹c₂›) { ‹t› } else { ‹f› }]
        | succ {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| succ ‹t₁›] [TyArith| succ ‹t₂›]
        | predZero: Eval₁ [TyArith| pred 0] [TyArith| 0]
        | predSucc {v: Term} (h₁: NatValue v): Eval₁ [TyArith| pred succ ‹v›] [TyArith| ‹v›]
        | pred {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| pred ‹t₁›] [TyArith| pred ‹t₂›]
        | isZeroZero: Eval₁ [TyArith| isZero 0] [TyArith| tru]
        | isZeroSucc {v: Term} (h₁: NatValue v): Eval₁ [TyArith| isZero succ ‹v›] [TyArith| fls]
        | isZero {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| isZero ‹t₁›] [TyArith| isZero ‹t₂›]
        | funny {c t₁ t₂ f: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| ite (‹c›) { ‹t₁› } else { ‹f› }] [TyArith| ite (‹c›) { ‹t₂› } else { ‹f› }]

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty := sorry
    end Variation3

    namespace Variation4
      inductive Eval₁: Term → Term → Prop where
        | iteTrue {t f: Term}: Eval₁ [TyArith| ite (tru) { ‹t› } else { ‹f› }] [TyArith| ‹t›]
        | iteFalse {t f: Term}: Eval₁ [TyArith| ite (fls) { ‹t› } else { ‹f› }] [TyArith| ‹f›]
        | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [TyArith| ite (‹c₁›) { ‹t› } else { ‹f› }] [TyArith| ite (‹c₂›) { ‹t› } else { ‹f› }]
        | succ {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| succ ‹t₁›] [TyArith| succ ‹t₂›]
        | predZero: Eval₁ [TyArith| pred 0] [TyArith| 0]
        | predSucc {v: Term} (h₁: NatValue v): Eval₁ [TyArith| pred succ ‹v›] [TyArith| ‹v›]
        | pred {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| pred ‹t₁›] [TyArith| pred ‹t₂›]
        | isZeroZero: Eval₁ [TyArith| isZero 0] [TyArith| tru]
        | isZeroSucc {v: Term} (h₁: NatValue v): Eval₁ [TyArith| isZero succ ‹v›] [TyArith| fls]
        | isZero {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [TyArith| isZero ‹t₁›] [TyArith| isZero ‹t₂›]
        | funny: Eval₁ [TyArith| pred fls] [TyArith| pred pred fls]

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty := sorry
    end Variation4

    namespace Variation5
      inductive HasType: Term → Ty → Prop where
        | true: HasType [TyArith| tru] .bool
        | false: HasType [TyArith| fls] .bool
        | ite {c t f: Term} {ty: Ty} (h₁: HasType c .bool) (h₂: HasType t ty) (h₂: HasType f ty): HasType [TyArith| ite (‹c›) { ‹t› } else { ‹f› }] ty
        | zero: HasType [TyArith| 0] .nat
        | succ {t: Term} (h₁: HasType t .nat): HasType [TyArith| succ ‹t›] .nat
        | pred {t: Term} (h₁: HasType t .nat): HasType [TyArith| pred ‹t›] .nat
        | isZero {t: Term} (h₁: HasType t .nat): HasType [TyArith| isZero ‹t›] .bool
        | funny: HasType [TyArith| 0] .bool

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty := sorry
    end Variation5

    namespace Variation6
      inductive HasType: Term → Ty → Prop where
        | true: HasType [TyArith| tru] .bool
        | false: HasType [TyArith| fls] .bool
        | ite {c t f: Term} {ty: Ty} (h₁: HasType c .bool) (h₂: HasType t ty) (h₂: HasType f ty): HasType [TyArith| ite (‹c›) { ‹t› } else { ‹f› }] ty
        | zero: HasType [TyArith| 0] .nat
        | succ {t: Term} (h₁: HasType t .nat): HasType [TyArith| succ ‹t›] .nat
        | pred {t: Term} (h₁: HasType t .nat): HasType [TyArith| pred ‹t›] .nat
        | isZero {t: Term} (h₁: HasType t .nat): HasType [TyArith| isZero ‹t›] .bool
        | funny: HasType [TyArith| pred 0] .bool

      theorem Eval₁.deterministic: SmallStep.Relation.deterministic Eval₁ := sorry
      theorem HasType.progress {t₁: Term} {ty: Ty}: (⊢ t₁ : ty) → Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
      theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (⊢ t₁ : ty) → Eval₁ t₁ t₂ → ⊢ t₂ : ty := sorry
    end Variation6

    -- TODO: Create Variation
    -- TODO: Remove Eval₁.predZero
    -- TODO: Big Step Semantics
  end Term

  namespace Tactic
  end Tactic

  namespace Blended
  end Blended
end SoftwareFoundations.ProgrammingLanguageFoundations.Types
