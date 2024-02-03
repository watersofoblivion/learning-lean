/-
# Small-Step Operational Semantics
-/

import SoftwareFoundations.LogicalFoundations.Imp

namespace SoftwareFoundations.ProgrammingLanguageFoundations.SmallStep
  /-
  ## A Toy Language
  -/

  inductive Term: Type where
    | const (n: Nat): Term
    | plus (t₁ t₂: Term): Term
  deriving Repr

  declare_syntax_cat toy

  syntax num : toy
  syntax:max "‹" term "›" : toy
  syntax:max "‹‹" term "››" : toy
  syntax:60 toy:60 "+" toy:61 : toy
  syntax "(" toy ")" : toy

  syntax "[Toy|" toy "]" : term

  macro_rules
    | `([Toy| $n:num])         => `(Term.const $n)
    | `([Toy| ‹ $n:term ›])    => `(Term.const $(Lean.quote n))
    | `([Toy| ‹‹ $t:term ›› ]) => `($(Lean.quote t))
    | `([Toy| $t₁ + $t₂])      => `(Term.plus [Toy| $t₁] [Toy| $t₂])
    | `([Toy| ( $t )])         => `([Toy| $t])

  def Term.eval: Term → Nat
    | .const n => n
    | .plus t₁ t₂ => t₁.eval + t₂.eval

  example: [Toy| (1 + 2) + (3 + 4)].eval = 10 := rfl

  inductive Eval: Term → Nat → Prop where
    | const {n: Nat}: Eval [Toy| ‹n›] n
    | plus {t₁ t₂: Term} {n₁ n₂: Nat}: Eval t₁ n₁ → Eval t₂ n₂ → Eval [Toy| ‹‹t₁››  + ‹‹t₂››] (n₁ + n₂)

  notation t "⇓" n => Eval t n

  namespace SimpleArith
    inductive Eval₁: Term → Term → Prop where
      | constConst {n₁ n₂: Nat}: Eval₁ [Toy| ‹n₁› + ‹n₂›] [Toy| ‹n₁ + n₂›]
      | plusL {t₁ t₂ t₃: Term} (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹t₁›› + ‹‹t₃››] [Toy| ‹‹t₂›› + ‹‹t₃››]
      | plusR {n: Nat} {t₁ t₂: Term} (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹n› + ‹‹t₁››] [Toy| ‹n› + ‹‹t₂››]

    scoped notation t₁ "⟶" t₂ => Eval₁ t₁ t₂

    namespace Term
      example: [Toy| (1 + 3) + (2 + 4)] ⟶ [Toy| 4 + (2 + 4)] :=
        .plusL .constConst

      example: [Toy| 0 + (2 + (1 + 3))] ⟶ [Toy| 0 + (2 + 4)] :=
        .plusR (.plusR .constConst)
    end Term

    namespace Tactic
      example: [Toy| (1 + 3) + (2 + 4)] ⟶ [Toy| 4 + (2 + 4)] := by
        apply Eval₁.plusL
        · apply Eval₁.constConst

      example: [Toy| 0 + (2 + (1 + 3))] ⟶ [Toy| 0 + (2 + 4)] := by
        apply Eval₁.plusR
        · apply Eval₁.plusR
          · apply Eval₁.constConst
    end Tactic

    namespace Blended
      example: [Toy| (1 + 3) + (2 + 4)] ⟶ [Toy| 4 + (2 + 4)] :=
        .plusL .constConst

      example: [Toy| 0 + (2 + (1 + 3))] ⟶ [Toy| 0 + (2 + 4)] :=
        .plusR (.plusR .constConst)
    end Blended
  end SimpleArith

  /-
  ## Relations
  -/

  def Relation (α: Type): Type := α → α → Prop

  def Relation.deterministic (R: Relation α): Prop := ∀ {x y₁ y₂: α}, (h₁: R x y₁) → (h₂: R x y₂) → y₁ = y₂

  namespace SimpleArith2
    open SimpleArith

    namespace Term
      theorem Eval₁.deterministic: Relation.deterministic Eval₁
        | _, _, _, .constConst, .constConst => rfl
        | _, _, _, .plusL h₁, .plusL h₂ =>
          have ih := deterministic h₁ h₂
          calc Term.plus _ _
            _ = Term.plus _ _ := congrFun (congrArg Term.plus ih) _
        | _, _, _, .plusR h₁, .plusR h₂ =>
          have ih := deterministic h₁ h₂
          calc Term.plus _ _
            _ = Term.plus _ _ := congrArg (Term.plus _) ih
    end Term

    namespace Tactic
      theorem Eval₁.deterministic: Relation.deterministic Eval₁ := by
        intro _ _ _
        intro h₁ h₂
        cases h₁ <;> cases h₂ <;> try (first | rfl
                                             | contradiction)
        case plusL.plusL _ _ _ h₁ _ h₂ => rw [deterministic h₁ h₂]
        case plusR.plusR _ _ _ h₁ _ h₂ => rw [deterministic h₁ h₂]
    end Tactic

    namespace Blended
      theorem Eval₁.deterministic: Relation.deterministic Eval₁
        | _, _, _, .constConst, .constConst => by rfl
        | _, _, _, .plusL h₁, .plusL h₂
        | _, _, _, .plusR h₁, .plusR h₂ => by rw [deterministic h₁ h₂]
    end Blended
  end SimpleArith2

  /-
  ### Values
  -/

  inductive Value: Term → Prop where
    | const (n: Nat): Value [Toy| ‹n›]

  inductive Eval₁: Term → Term → Prop where
    | constConst {n₁ n₂: Nat}: Eval₁ [Toy| ‹n₁› + ‹n₂›] [Toy| ‹n₁ + n₂›]
    | plusL {t₁ t₂ t₃: Term} (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹t₁›› + ‹‹t₃››] [Toy| ‹‹t₂›› + ‹‹t₃››]
    | plusR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹v₁›› + ‹‹t₁››] [Toy| ‹‹v₁›› + ‹‹t₂››]

  notation t₁ "⟶" t₂ => Eval₁ t₁ t₂

  namespace Term
    theorem Eval₁.deterministic: Relation.deterministic Eval₁
      | _, _, _, .constConst, .constConst => rfl
      | _, _, _, .plusL h₁, .plusL h₂ =>
        have ih := deterministic h₁ h₂
        calc Term.plus _ _
          _ = Term.plus _ _ := congrFun (congrArg Term.plus ih) _
      | _, _, _, .plusR (.const _) h₁, .plusL h₂ => sorry
      | _, _, _, .plusR _ h₁, .plusR _ h₂ =>
        have ih := deterministic h₁ h₂
        calc Term.plus _ _
          _ = Term.plus _ _ := congrArg (Term.plus _) ih
  end Term

  namespace Tactic
    theorem Eval₁.deterministic: Relation.deterministic Eval₁ := by
      intro _ _ _
      intro h₁ h₂
      cases h₁ <;> cases h₂ <;> try (first | rfl
                                           | contradiction)
      case plusL.plusL _ _ _ h₁ _ h₂    => rw [deterministic h₁ h₂]
      case plusR.plusR _ _ _ h₁ _ _ h₂  => rw [deterministic h₁ h₂]
      case plusL.plusR _ _ _ h₁ _ hv h₂ =>
        cases hv with
          | const => contradiction
      case plusR.plusL _ _ _ hv h₁ _ h₂ =>
        cases hv with
          | const => contradiction
  end Tactic

  namespace Blended
    theorem Eval₁.deterministic: Relation.deterministic Eval₁
      | _, _, _, .constConst, .constConst       => by rfl
      | _, _, _, .plusL h₁, .plusL h₂           => by rw [deterministic h₁ h₂]
      | _, _, _, .plusR _ h₁, .plusR _ h₂       => by rw [deterministic h₁ h₂]
      | _, _, _, .plusR (.const _) _, .plusL h₂ => by contradiction
  end Blended

  /-
  ### Strong Progress and Normal Forms
  -/

  namespace Term
    theorem Eval₁.strong_progress: ∀ t₁: Term, Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂
      | .const n => .inl (.const n)
      | .plus t₁ t₂ =>
        match strong_progress t₁, strong_progress t₂ with
          | .inl (.const n₁), .inl (.const n₂) => .inr ⟨.const (n₁ + n₂), .constConst⟩
          | .inl (.const n₁), .inr ⟨t₃, hw⟩    => .inr ⟨.plus (.const n₁) t₃, .plusR (.const n₁) hw⟩
          | .inr ⟨t₃, hw⟩, _                   => .inr ⟨.plus t₃ t₂, .plusL hw⟩
  end Term

  namespace Tactic
    theorem Eval₁.strong_progress: ∀ t₁: Term, Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂ := by
      intro t₁
      induction t₁ with
        | const n =>
          apply Or.inl
          · apply Value.const
        | plus t₁ t₂ ih₁ ih₂ =>
          cases ih₁ with
            | inr ex =>
              apply Or.inr
              cases ex with
                | intro w hw =>
                  exists (.plus w t₂)
                  · apply Eval₁.plusL
                    · exact hw
            | inl hv₁ =>
              cases ih₂ with
                | inr ex =>
                  apply Or.inr
                  cases ex with
                    | intro w hw =>
                      exists (.plus t₁ w)
                      · apply Eval₁.plusR
                        · exact hv₁
                        · exact hw
                | inl hv₂ =>
                  cases t₁ with
                    | plus _ _ => contradiction
                    | const n₁ =>
                      cases t₂ with
                        | plus _ _ => contradiction
                        | const n₂ =>
                          apply Or.inr
                          · apply Exists.intro
                            · apply Eval₁.constConst
  end Tactic

  namespace Blended
    theorem Eval₁.strong_progress: ∀ t₁: Term, Value t₁ ∨ ∃ t₂: Term, t₁ ⟶ t₂
      | .const n => .inl (.const n)
      | .plus t₁ t₂ =>
        match strong_progress t₁, strong_progress t₂ with
          | .inl (.const n₁), .inl (.const n₂) => .inr ⟨.const (n₁ + n₂), .constConst⟩
          | .inl (.const n₁), .inr ⟨t₃, hw⟩    => .inr ⟨.plus (.const n₁) t₃, .plusR (.const n₁) hw⟩
          | .inr ⟨t₃, hw⟩, _                   => .inr ⟨.plus t₃ t₂, .plusL hw⟩
  end Blended

  def Relation.normal (R: Relation α) (t₁: α): Prop := ¬ ∃ t₂: α, R t₁ t₂

  namespace Term
    theorem Value.normal {v: Term}: Value v → Relation.normal Eval₁ v
      | .const n₁, ⟨w, hw⟩ =>
        -- by contradiction
        sorry

    theorem Relation.normal.value {t: Term}: Relation.normal Eval₁ t → Value t
      | hn =>
        match Eval₁.strong_progress t with
          | .inl hv => hv
          | .inr hex => absurd hex hn

    theorem normal_value {t: Term}: Relation.normal Eval₁ t ↔ Value t :=
      ⟨Relation.normal.value, Value.normal⟩
  end Term

  namespace Tactic
    theorem Value.normal {v: Term}: Value v → Relation.normal Eval₁ v := by
      intro hv
      intro
      | .intro w hw =>
        cases hv with
          | const n => contradiction

    theorem Relation.normal.value {t: Term}: Relation.normal Eval₁ t → Value t := by
      intro hn
      have h: Value t ∨ ∃ t₂: Term, t ⟶ t₂ := by
        apply Eval₁.strong_progress
      cases h with
        | inl _ => assumption
        | inr _ => contradiction

    theorem normal_value {t: Term}: Relation.normal Eval₁ t ↔ Value t := by
      apply Iff.intro
      · exact Relation.normal.value
      · exact Value.normal
  end Tactic

  namespace Blended
    theorem Value.normal {v: Term}: Value v → Relation.normal Eval₁ v
      | .const n₁, ⟨.const n₂, hw⟩ => by contradiction

    theorem Relation.normal.value {t: Term}: Relation.normal Eval₁ t → Value t
      | hn =>
        match Eval₁.strong_progress t with
          | .inl hv => hv
          | .inr hex => absurd hex hn

    theorem normal_value {t: Term}: Relation.normal Eval₁ t ↔ Value t :=
      ⟨Relation.normal.value, Value.normal⟩
  end Blended

  namespace Temp1
    inductive Value: Term → Prop where
      | const (n: Nat): Value [Toy| ‹n›]
      | funny (t₁: Term) (n: Nat): Value [Toy| ‹‹t₁›› + ‹n›]

    inductive Eval₁: Term → Term → Prop where
      | constConst {n₁ n₂: Nat}: Eval₁ [Toy| ‹n₁› + ‹n₂›] [Toy| ‹n₁ + n₂›]
      | plusL {t₁ t₂ t₃: Term} (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹t₁›› + ‹‹t₃››] [Toy| ‹‹t₂›› + ‹‹t₃››]
      | plusR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹v₁›› + ‹‹t₁››] [Toy| ‹‹v₁›› + ‹‹t₂››]

    notation t₁ "⟶" t₂ => Eval₁ t₁ t₂

    -- def Relation.normal (R: Relation α) (t₁: α): Prop := ¬ ∃ t₂: α, R t₁ t₂

    namespace Term
      theorem value_not_normal_form: ∃ v: Term, Value v ∧ ¬Relation.normal Eval₁ v :=
        have hwv := .funny [Toy| 1 + 2] 3
        have hwnn
          | hn => hn ⟨[Toy| 3 + 3], .plusL .constConst⟩
        ⟨[Toy| (1 + 2) + 3], ⟨hwv, hwnn⟩⟩
    end Term

    namespace Tactic
      theorem value_not_normal_form: ∃ v: Term, Value v ∧ ¬Relation.normal Eval₁ v := by
        apply Exists.intro
        · apply And.intro
          · apply Value.funny
            · exact [Toy| 1 + 2]
            · exact 3
          . unfold Relation.normal
            intro hn
            apply hn
            · apply Exists.intro
              · apply Eval₁.plusL
                · apply Eval₁.constConst
    end Tactic

    namespace Blended
      theorem value_not_normal_form: ∃ v: Term, Value v ∧ ¬Relation.normal Eval₁ v :=
        have hwv := .funny [Toy| 1 + 2] 3
        have hwnn
          | hn => hn ⟨[Toy| 3 + 3], .plusL .constConst⟩
        ⟨[Toy| (1 + 2) + 3], ⟨hwv, hwnn⟩⟩
    end Blended
  end Temp1

  namespace Temp2
    inductive Value: Term → Prop where
      | const (n: Nat): Value [Toy| ‹n›]

    inductive Eval₁: Term → Term → Prop where
      | funny {n: Nat}: Eval₁ [Toy| ‹n›] [Toy| ‹n› + 0]
      | constConst {n₁ n₂: Nat}: Eval₁ [Toy| ‹n₁› + ‹n₂›] [Toy| ‹n₁ + n₂›]
      | plusL {t₁ t₂ t₃: Term} (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹t₁›› + ‹‹t₃››] [Toy| ‹‹t₂›› + ‹‹t₃››]
      | plusR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹v₁›› + ‹‹t₁››] [Toy| ‹‹v₁›› + ‹‹t₂››]

    notation t₁ "⟶" t₂ => Eval₁ t₁ t₂

    -- def Relation.normal (R: Relation α) (t₁: α): Prop := ¬ ∃ t₂: α, R t₁ t₂

    namespace Term
      theorem value_not_normal_form: ∃ v: Term, Value v ∧ ¬Relation.normal Eval₁ v :=
        have hv := .const 1
        have hnn
          | hn => hn ⟨[Toy| 1 + 0], .funny⟩
        ⟨[Toy| 1], ⟨hv, hnn⟩⟩
    end Term

    namespace Tactic
      theorem value_not_normal_form: ∃ v: Term, Value v ∧ ¬Relation.normal Eval₁ v := by
        apply Exists.intro
        · apply And.intro
          · apply Value.const
            · exact 1
          . unfold Relation.normal
            intro hn
            apply hn
            · apply Exists.intro
              · apply Eval₁.funny
    end Tactic

    namespace Blended
      theorem value_not_normal_form: ∃ v: Term, Value v ∧ ¬Relation.normal Eval₁ v :=
        have hv := .const 1
        have hnn
          | hn => hn ⟨[Toy| 1 + 0], .funny⟩
        ⟨[Toy| 1], ⟨hv, hnn⟩⟩
    end Blended
  end Temp2

  namespace Temp3
    inductive Value: Term → Prop where
      | const (n: Nat): Value [Toy| ‹n›]

    inductive Eval₁: Term → Term → Prop where
      | constConst {n₁ n₂: Nat}: Eval₁ [Toy| ‹n₁› + ‹n₂›] [Toy| ‹n₁ + n₂›]
      | plusL {t₁ t₂ t₃: Term} (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹t₁›› + ‹‹t₃››] [Toy| ‹‹t₂›› + ‹‹t₃››]

    notation t₁ "⟶" t₂ => Eval₁ t₁ t₂

    -- def Relation.normal (R: Relation α) (t₁: α): Prop := ¬ ∃ t₂: α, R t₁ t₂

    namespace Term
      theorem value_not_normal_form: ∃ v: Term, ¬Value v ∧ Relation.normal Eval₁ v :=
        have hnv
          | hv => sorry
        have hn
          | ⟨w, hnw⟩ => sorry
        ⟨[Toy| 1 + (2 + 3)], ⟨hnv, hn⟩⟩
    end Term

    namespace Tactic
      theorem value_not_normal_form: ∃ v: Term, ¬Value v ∧ Relation.normal Eval₁ v := by
        apply Exists.intro
        · apply And.intro
          · intro hnv
            sorry
          · unfold Relation.normal
            intro hn
            sorry
        sorry
    end Tactic

    namespace Blended
      theorem value_not_normal_form: ∃ v: Term, ¬Value v ∧ Relation.normal Eval₁ v := sorry
    end Blended
  end Temp3

  namespace Temp4
    inductive Term: Type where
      | true: Term
      | false: Term
      | test: Term → Term → Term → Term

    declare_syntax_cat tf

    syntax "tru" : tf
    syntax "fls" : tf
    syntax:max "‹" term "›" : tf
    syntax "test" "(" tf ")" "{" tf "}" "else" "{" tf "}" : tf
    syntax "(" tf ")" : tf

    syntax "[TF|" tf "]" : term

    macro_rules
      | `([TF| tru])                            => `(Term.true)
      | `([TF| fls])                            => `(Term.false)
      | `([TF| ‹ true ›])                       => `(Term.const true)
      | `([TF| ‹ false ›])                      => `(Term.const false)
      | `([TF| ‹ $t:term ›])                    => `($(Lean.quote t))
      | `([TF| test ( $c ) { $t } else { $f }]) => `(Term.test [TF| $c] [TF| $t] [TF| $f])
      | `([TF| ( $t )])                         => `([TF| $t])

    inductive Value: Term → Prop where
      | true: Value .true
      | false: Value .false

    inductive Eval₁: Term → Term → Prop where
      | testTrue {t f: Term}: Eval₁ [TF| test (tru) { ‹t› } else { ‹f› }] t
      | testFalse {t f: Term}: Eval₁ [TF| test (fls) { ‹t› } else { ‹f› }] f
      | test {c₁ c₂ t f: Term} (h: Eval₁ c₁ c₂): Eval₁ [TF| test (‹c₁›) { ‹t› } else { ‹f› }] [TF| test (‹c₂›) { ‹t› } else { ‹f› }]

    notation t₁ "⟶" t₂ => Eval₁ t₁ t₂

    -- TODO: Which propositions are provable

    namespace Term
      theorem Eval₁.strong_progress: ∀ t₁: Term, Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂
        | .true => .inl .true
        | .false => .inl .false
        | .test c t f =>
          match strong_progress c with
            | .inl .true   => .inr ⟨[TF| ‹t›], .testTrue⟩
            | .inl .false  => .inr ⟨[TF| ‹f›], .testFalse⟩
            | .inr ⟨w, hw⟩ => .inr ⟨[TF| test (‹w›) { ‹t› } else { ‹f› }], .test hw⟩

      theorem Eval₁.deterministic: Relation.deterministic Eval₁
        | _, _, _, .testTrue, .testTrue
        | _, _, _, .testFalse, .testFalse => rfl
        | _, _, _, .test h₁, .test h₂ =>
          have ih := deterministic h₁ h₂
          calc Term.test _ _ _
            _ = Term.test _ _ _ := congrFun (congrFun (congrArg Term.test ih) _) _
    end Term

    namespace Tactic
      theorem Eval₁.strong_progress (t₁: Term): Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := by
        induction t₁ with
          | true =>
            apply Or.inl
            · apply Value.true
          | false =>
            apply Or.inl
            · apply Value.false
          | «test» c t f ih =>
            cases ih with
              | inl v =>
                cases v with
                  | true =>
                    apply Or.inr
                    · exists [TF| ‹t›]
                      · apply Eval₁.testTrue
                  | false =>
                    apply Or.inr
                    · exists [TF| ‹f›]
                      · apply Eval₁.testFalse
              | inr ex =>
                cases ex with
                  | intro w hw =>
                    apply Or.inr
                    · exists [TF| test (‹w›) { ‹t› } else { ‹f› }]
                      · apply Eval₁.test
                        · exact hw

      theorem Eval₁.deterministic: Relation.deterministic Eval₁ := by
        intro _ _ _ h₁ h₂
        cases h₁ <;> cases h₂ <;> try (first | rfl
                                             | contradiction)
        case test.test _ _ _ _ h₁ _ h₂ => rw [deterministic h₁ h₂]
    end Tactic

    namespace Blended
      theorem Eval₁.strong_progress: ∀ t₁: Term, Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂
        | .true => .inl .true
        | .false => .inl .false
        | .test c t f =>
          match strong_progress c with
            | .inl .true   => .inr ⟨[TF| ‹t›], .testTrue⟩
            | .inl .false  => .inr ⟨[TF| ‹f›], .testFalse⟩
            | .inr ⟨w, hw⟩ => .inr ⟨[TF| test (‹w›) { ‹t›} else { ‹f› }], .test hw⟩

      theorem Eval₁.deterministic: Relation.deterministic Eval₁
        | _, _, _, .testTrue, .testTrue => rfl
        | _, _, _, .testFalse, .testFalse => rfl
        | _, _, _, .test h₁, .test h₂ => by rw [deterministic h₁ h₂]
    end Blended

    namespace Temp5
      inductive Eval₁: Term → Term → Prop where
        | testTrue {t f: Term}: Eval₁ [TF| test (tru) { ‹t› } else { ‹f› }] t
        | testFalse {t f: Term}: Eval₁ [TF| test (fls) { ‹t› } else { ‹f› }] f
        | test {c₁ c₂ t f: Term} (h: Eval₁ c₁ c₂): Eval₁ [TF| test (‹c₁›) { ‹t› } else { ‹f› }] [TF| test (‹c₂›) { ‹t› } else { ‹f› }]
        | shortCircuit {c t₁ t₂ f₁ f₂} (h₁: Eval₁ t₁ t₂) (h₂: Eval₁ f₁ f₂) (h₃: t₂ = f₂): Eval₁ [TF| test (‹c›) { ‹t₁› } else { ‹f₁› }] t₁

      notation t₁ "⟶" t₂ => Eval₁ t₁ t₂

      -- TODO
    end Temp5
  end Temp4

  /-
  ## Multi-Step Reduction
  -/

  inductive MultiStep (R: Relation α): Relation α where
    | refl {x: α}: MultiStep R x x
    | step {x₁ x₂ x₃: α} (h₁: R x₁ x₂) (h₂: MultiStep R x₂ x₃): MultiStep R x₁ x₃

  -- Allows the use of `calc` proofs
  instance (R: Relation α): Trans R R (MultiStep R) where
    trans h₁ h₂ := .step h₁ (.step h₂ .refl)
  instance: Trans R (MultiStep R) (MultiStep R) where
    trans h₁ h₂ := .step h₁ h₂
  instance: Trans (MultiStep R) R (MultiStep R) where
    -- This can't be done term-style and has to be done with tactics because of
    -- shortcomings in the Lean equation compiler.  See
    -- [this GitHub issue](https://github.com/leanprover/lean4/pull/1672)
    trans h₁ h₂ := by
      induction h₁ with
        | refl =>
          apply MultiStep.step
          · exact h₂
          · apply MultiStep.refl
        | step h₁ _ ih =>
          apply MultiStep.step
          · exact h₁
          · apply ih
            · exact h₂
  instance: Trans (MultiStep R) (MultiStep R) (MultiStep R) where
    -- This can't be done term-style and has to be done with tactics because of
    -- shortcomings in the Lean equation compiler.  See
    -- [this GitHub issue](https://github.com/leanprover/lean4/pull/1672)
    trans h₁ h₂ := by
      induction h₁ with
        | refl => exact h₂
        | step h₁ _ ih =>
          apply MultiStep.step
          · exact h₁
          · apply ih
            · exact h₂

  notation t₁ "↠" t₂ => MultiStep Eval₁ t₁ t₂
  infix:50 "⇒" => Eval₁

  namespace Term
    theorem MultiStep.contains_R {R: Relation α} {x₁ x₂: α}: R x y → MultiStep R x y
      | h => .step h .refl

    -- This can't be done term-style and has to be done with tactics because of
    -- shortcomings in the Lean equation compiler.  See
    -- [this GitHub issue](https://github.com/leanprover/lean4/pull/1672)
    theorem MultiStep.transitive {R: Relation α} {x₁ x₂ x₃: α}: MultiStep R x₁ x₂ → MultiStep R x₂ x₃ → MultiStep R x₁ x₃ := sorry
  end Term

  namespace Tactic
    theorem MultiStep.contains_R {R: Relation α} {x₁ x₂: α} (h: R x y): MultiStep R x y := by
      apply MultiStep.step
      · exact h
      · apply MultiStep.refl

    theorem MultiStep.transitive {R: Relation α} {x₁ x₂ x₃: α} (h₁: MultiStep R x₁ x₂) (h₂: MultiStep R x₂ x₃): MultiStep R x₁ x₃ := by
      induction h₁ with
        | refl => exact h₂
        | step h₁ _ ih =>
          apply MultiStep.step
          · exact h₁
          · apply ih
            · exact h₂
  end Tactic

  namespace Blended
    theorem MultiStep.contains_R {R: Relation α} {x₁ x₂: α}: R x y → MultiStep R x y
      | h => .step h .refl

    -- This can't be done term-style and has to be done with tactics because of
    -- shortcomings in the Lean equation compiler.  See
    -- [this GitHub issue](https://github.com/leanprover/lean4/pull/1672)
    theorem MultiStep.transitive {R: Relation α} {x₁ x₂ x₃: α}: MultiStep R x₁ x₂ → MultiStep R x₂ x₃ → MultiStep R x₁ x₃ := sorry
  end Blended

  /-
  ### Examples
  -/

  namespace Term
    example: [Toy| (0 + 3) + (2 + 4)] ↠ [Toy| ‹(0 + 3) + (2 + 4)›] :=
      calc [Toy| (0 + 3) + (2 + 4)]
        _ ⇒ [Toy| 3 + (2 + 4)] := .plusL .constConst
        _ ⇒ [Toy| 3 + 6]       := .plusR (.const 3) .constConst
        _ ⇒ [Toy| 9]           := .constConst

    example: [Toy| 3]     ↠ [Toy| 3]     := .refl
    example: [Toy| 0 + 3] ↠ [Toy| 0 + 3] := .refl

    example: [Toy| 0 + (2 + (0 + 3))] ↠ [Toy| 0 + ‹2 + (0 + 3)›] :=
      calc [Toy| 0 + (2 + (0 + 3))]
        _ ⇒ [Toy| 0 + (2 + 3)] := .plusR (.const 0) (.plusR (.const 2) .constConst)
        _ ⇒ [Toy| 0 + 5]       := .plusR (.const 0) .constConst
  end Term

  namespace Tactic
    example: [Toy| (0 + 3) + (2 + 4)] ↠ [Toy| ‹(0 + 3) + (2 + 4)›] := by
      apply MultiStep.step
      · apply Eval₁.plusL
        · apply Eval₁.constConst
      · apply MultiStep.step
        · apply Eval₁.plusR
          . apply Value.const
          · apply Eval₁.constConst
        · apply MultiStep.step
          · apply Eval₁.constConst
          . apply MultiStep.refl

    example: [Toy| 3] ↠ [Toy| 3] := by
      apply MultiStep.refl

    example: [Toy| 0 + 3] ↠ [Toy| 0 + 3] := by
      apply MultiStep.refl

    example: [Toy| 0 + (2 + (0 + 3))] ↠ [Toy| 0 + ‹2 + (0 + 3)›] := by
      apply MultiStep.step
      · apply Eval₁.plusR
        · apply Value.const
        · apply Eval₁.plusR
          · apply Value.const
          · apply Eval₁.constConst
      · apply MultiStep.step
        · apply Eval₁.plusR
          · apply Value.const
          · apply Eval₁.constConst
        · apply MultiStep.refl
  end Tactic

  namespace Blended
    example: [Toy| (0 + 3) + (2 + 4)] ↠ [Toy| ‹(0 + 3) + (2 + 4)›] :=
      calc [Toy| (0 + 3) + (2 + 4)]
        _ ⇒ [Toy| 3 + (2 + 4)] := .plusL .constConst
        _ ⇒ [Toy| 3 + 6]       := .plusR (.const 3) .constConst
        _ ⇒ [Toy| 9]           := .constConst

    example: [Toy| 3]     ↠ [Toy| 3]     := .refl
    example: [Toy| 0 + 3] ↠ [Toy| 0 + 3] := .refl

    example: [Toy| 0 + (2 + (0 + 3))] ↠ [Toy| 0 + ‹2 + (0 + 3)›] :=
      calc [Toy| 0 + (2 + (0 + 3))]
        _ ⇒ [Toy| 0 + (2 + 3)] := .plusR (.const 0) (.plusR (.const 2) .constConst)
        _ ⇒ [Toy| 0 + 5]       := .plusR (.const 0) .constConst
  end Blended

  /-
  ### Normal Forms, Again
  -/

  def Eval₁.normal: Term → Prop := Relation.normal Eval₁

  def Term.normalOf (t₁ t₂: Term): Prop := Eval₁ t₂ t₁ ∧ Eval₁.normal t₁

  namespace Term
    theorem Eval₁.normal.unique: Relation.deterministic Term.normalOf
      | t₁, t₂, t₃, ⟨he₁, hn₁⟩, ⟨he₂, hn₂⟩ =>
        have h₃: t₂ = t₁ :=
          calc t₂
            _ ⇒ t₁ := he₁
            _ = t₁ := sorry
        have h₄: t₃ = t₁ :=
          calc t₃
            _ ⇒ t₁ := he₂
            _ = t₁ := sorry
        calc t₂
          _ = t₁ := h₃
          _ = t₃ := Eq.symm h₄
  end Term

  namespace Tactic
    theorem Eval₁.normal.unique: Relation.deterministic Term.normalOf := by sorry
  end Tactic

  namespace Blended
    theorem Eval₁.normal.unique: Relation.deterministic Term.normalOf
      | t₁, t₂, t₃, h₁, h₂ =>
        have h₃ :=
          calc t₂
            _ = t₁ := sorry
        have h₄ :=
          calc t₃
            _ = t₁ := sorry
        by rw [h₃, h₄]
  end Blended

  def Relation.normalizing (R: Relation α): Prop := ∀ t₁: α, ∃ t₂: α, MultiStep R t₁ t₂ ∧ Relation.normal R t₂

  namespace Term
    theorem Eval₁.normalizing: Relation.normalizing Eval₁
      | .const n =>
        have hn := Value.normal (.const n)
        ⟨[Toy| ‹n›], ⟨.refl, hn⟩⟩
      | .plus t₁ t₂ =>
        have ⟨nt₁, ⟨w₁, hw₁⟩⟩ := normalizing t₁
        have ⟨nt₂, ⟨w₂, hw₂⟩⟩ := normalizing t₂
        match nt₁, nt₂ with
          | .const n₁, const n₂ => sorry
          | _, _ => sorry
      where
        plusL_normalizing (t₁ t₂ t₃: Term) (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹t₁›› + ‹‹t₃››] [Toy| ‹‹t₂›› + ‹‹t₃››] := sorry
        plusR_normalizing (v₁ t₁ t₂: Term) (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹v₁›› + ‹‹t₁››] [Toy| ‹‹v₁›› + ‹‹t₂››] := sorry
  end Term

  namespace Tactic
    theorem Eval₁.normalizing: Relation.normalizing Eval₁ := by
      sorry
      where
        plusL_normalizing (t₁ t₂ t₃: Term) (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹t₁›› + ‹‹t₃››] [Toy| ‹‹t₂›› + ‹‹t₃››] := by sorry
        plusR_normalizing (v₁ t₁ t₂: Term) (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹v₁›› + ‹‹t₁››] [Toy| ‹‹v₁›› + ‹‹t₂››] := by sorry
  end Tactic

  namespace Blended
    theorem Eval₁.normalizing: Relation.normalizing Eval₁ :=
      sorry
      where
        plusL_normalizing (t₁ t₂ t₃: Term) (h: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹t₁›› + ‹‹t₃››] [Toy| ‹‹t₂›› + ‹‹t₃››] := sorry
        plusR_normalizing (v₁ t₁ t₂: Term) (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Toy| ‹‹v₁›› + ‹‹t₁››] [Toy| ‹‹v₁›› + ‹‹t₂››] := sorry
  end Blended

  /-
  ### Equivalence of Big-Step and Small-Step
  -/

  namespace Term
    theorem Eval₁.equiv_multistep (t: Term) (n: Nat): t.eval == n → MultiStep Eval₁ t [Toy| ‹n›]
      | h => sorry
  end Term

  /-
  ### Additional Exercises
  -/

  namespace Combined
    inductive Term: Type where
      | const (n: Nat): Term
      | plus (t₁ t₂: Term): Term
      | true: Term
      | false: Term
      | test: Term → Term → Term → Term

    declare_syntax_cat combined

    syntax num : combined
    syntax "tru" : combined
    syntax "fls" : combined
    syntax:max "‹nat:" term "›" : combined
    syntax:max "‹bool:" term "›" : combined
    syntax:max "‹‹" term "››" : combined
    syntax:60 combined:60 "+" combined:61 : combined
    syntax "test" "(" combined ")" "{" combined "}" "else" "{" combined "}" : combined
    syntax "(" combined ")" : combined

    syntax "[Combined|" combined "]" : term

    macro_rules
      | `([Combined| tru])                            => `(Term.true)
      | `([Combined| fls])                            => `(Term.true)
      | `([Combined| ‹nat: $n:term ›])                => `(Term.const $(Lean.quote n))
      | `([Combined| ‹bool: true ›])                  => `(Term.true)
      | `([Combined| ‹bool: false ›])                 => `(Term.false)
      | `([Combined| ‹‹ $t:term ›› ])                 => `($(Lean.quote t))
      | `([Combined| $t₁ + $t₂])                      => `(Term.plus [Combined| $t₁] [Combined| $t₂])
      | `([Combined| test ( $c ) { $t } else { $f }]) => `(Term.test [Combined| $c] [Combined| $t] [Combined| $f])
      | `([Combined| ( $t )])                         => `([Combined| $t])

    inductive Value: Term → Prop where
      | true: Value [Combined| tru]
      | false: Value [Combined| fls]
      | const (n: Nat): Value [Combined| ‹nat:n›]

    inductive Eval₁: Term → Term → Prop where
      | constConst {n₁ n₂: Nat}: Eval₁ [Combined| ‹nat:n₁› + ‹nat:n₂›] [Combined| ‹nat:n₁ + n₂›]
      | plusL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Combined| ‹‹t₁›› + ‹‹t₃››] [Combined| ‹‹t₂›› + ‹‹t₃››]
      | plusR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Combined| ‹‹v₁›› + ‹‹t₁››] [Combined| ‹‹v₁›› + ‹‹t₂››]
      | testTrue {t f: Term}: Eval₁ [Combined| test (tru) { ‹‹t›› } else { ‹‹f›› }] [Combined| ‹‹t››]
      | testFalse {t f: Term}: Eval₁ [Combined| test (fls) { ‹‹t›› } else { ‹‹f›› }] [Combined| ‹‹f››]
      | test {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [Combined| test (‹‹c₁››) { ‹‹t›› } else { ‹‹f›› }] [Combined| test (‹‹c₂››) { ‹‹t›› } else { ‹‹f›› }]

    namespace Term
      theorem Eval₁.deterministic: Relation.deterministic Eval₁ := sorry
      theorem Eval₁.strong_progress: ((t₁: Term) → Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂) ∨ ¬((t₁: Term) → Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂) := sorry
    end Term

    namespace Tactic
      theorem Eval₁.deterministic: Relation.deterministic Eval₁ := by sorry
      theorem Eval₁.strong_progress: ((t₁: Term) → Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂) ∨ ¬((t₁: Term) → Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂) := by sorry
    end Tactic

    namespace Blended
      theorem Eval₁.deterministic: Relation.deterministic Eval₁ := sorry
      theorem Eval₁.strong_progress: ((t₁: Term) → Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂) ∨ ¬((t₁: Term) → Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂) := sorry
    end Blended
  end Combined

  /-
  ## Small-Step Imp
  -/

  open Imp

  abbrev State := _root_.SoftwareFoundations.LogicalFoundations.Imp.State
  abbrev Arith := _root_.SoftwareFoundations.LogicalFoundations.Imp.Arith
  abbrev Logic := _root_.SoftwareFoundations.LogicalFoundations.Imp.Logic
  abbrev Command := _root_.SoftwareFoundations.LogicalFoundations.Imp.Command

  inductive ArithValue: Arith → Prop where
    | const (n: Nat): ArithValue [Arith| ‹num:n›]

  inductive LogicValue: Logic → Prop where
    | true: LogicValue [Logic| tru]
    | false: LogicValue [Logic| fls]

  inductive ArithEval₁ (s: State): Arith → Arith → Prop where
    | ident {id: String}: ArithEval₁ s [Arith| ‹id:id›] [Arith| ‹num:(s id)›]
    | plusL {e₁ e₂ e₃: Arith} (h₁: ArithEval₁ s e₁ e₂): ArithEval₁ s [Arith| ‹e₁› + ‹e₃›] [Arith| ‹e₂› + ‹e₃›]
    | plusR {v₁ e₁ e₂: Arith} (h₁: ArithValue v₁) (h₂: ArithEval₁ s e₁ e₂): ArithEval₁ s [Arith| ‹v₁› + ‹e₁›] [Arith| ‹v₁› + ‹e₂›]
    | plus {v₁ v₂: Nat}: ArithEval₁ s [Arith| ‹num:v₁› + ‹num:v₂›] [Arith| ‹num:v₁ + v₂›]
    | minusL {e₁ e₂ e₃: Arith} (h₁: ArithEval₁ s e₁ e₂): ArithEval₁ s [Arith| ‹e₁› - ‹e₃›] [Arith| ‹e₂› - ‹e₃›]
    | minusR {v₁ e₁ e₂: Arith} (h₁: ArithValue v₁) (h₂: ArithEval₁ s e₁ e₂): ArithEval₁ s [Arith| ‹v₁› - ‹e₁›] [Arith| ‹v₁› - ‹e₂›]
    | minus {v₁ v₂: Nat}: ArithEval₁ s [Arith| ‹num:v₁› - ‹num:v₂›] [Arith| ‹num:v₁ - v₂›]
    | multL {e₁ e₂ e₃: Arith} (h₁: ArithEval₁ s e₁ e₂): ArithEval₁ s [Arith| ‹e₁› * ‹e₃›] [Arith| ‹e₂› * ‹e₃›]
    | multR {v₁ e₁ e₂: Arith} (h₁: ArithValue v₁) (h₂: ArithEval₁ s e₁ e₂): ArithEval₁ s [Arith| ‹v₁› * ‹e₁›] [Arith| ‹v₁› * ‹e₂›]
    | mult {v₁ v₂: Nat}: ArithEval₁ s [Arith| ‹num:v₁› * ‹num:v₂›] [Arith| ‹num:v₁ * v₂›]

  inductive LogicEval₁ (s: State): Logic → Logic → Prop where
    | eqL {e₁ e₂ e₃: Arith} (h₁: ArithEval₁ s e₁ e₂): LogicEval₁ s [Logic| ‹e₁› = ‹e₃›] [Logic| ‹e₂› = ‹e₃›]
    | eqR {v₁ e₁ e₂: Arith} (h₁: ArithEval₁ s e₁ e₂): LogicEval₁ s [Logic| ‹v₁› = ‹e₁›] [Logic| ‹v₁› = ‹e₂›]
    | eq {v₁ v₂: Nat}: LogicEval₁ s [Logic| ‹num:v₁› = ‹num:v₂›] [Logic| ‹‹v₁ == v₂››]
    | neqL {e₁ e₂ e₃: Arith} (h₁: ArithEval₁ s e₁ e₂): LogicEval₁ s [Logic| ‹e₁› ≠ ‹e₃›] [Logic| ‹e₂› ≠ ‹e₃›]
    | neqR {v₁ e₁ e₂: Arith} (h₁: ArithValue v₁) (h₂: ArithEval₁ s e₁ e₂): LogicEval₁ s [Logic| ‹v₁› ≠ ‹e₁›] [Logic| ‹v₁› ≠ ‹e₂›]
    | neq {v₁ v₂: Nat}: LogicEval₁ s [Logic| ‹num:v₁› ≠ ‹num:v₂›] [Logic| ‹‹v₁ != v₂››]
    | leL {e₁ e₂ e₃: Arith} (h₁: ArithEval₁ s e₁ e₂): LogicEval₁ s [Logic| ‹e₁› ≤ ‹e₃›] [Logic| ‹e₂› ≤ ‹e₃›]
    | leR {v₁ e₁ e₂: Arith} (h₁: ArithValue v₁) (h₂: ArithEval₁ s e₁ e₂): LogicEval₁ s [Logic| ‹v₁› ≤ ‹e₁›] [Logic| ‹v₁› ≤ ‹e₂›]
    | le {v₁ v₂: Nat}: LogicEval₁ s [Logic| ‹num:v₁› ≤ ‹num:v₂›] [Logic| ‹‹v₁ ≤ v₂››]
    | gtL {e₁ e₂ e₃: Arith} (h₁: ArithEval₁ s e₁ e₂): LogicEval₁ s [Logic| ‹e₁› > ‹e₃›] [Logic| ‹e₂› > ‹e₃›]
    | gtR {v₁ e₁ e₂: Arith} (h₁: ArithValue v₁) (h₂: ArithEval₁ s e₁ e₂): LogicEval₁ s [Logic| ‹v₁› > ‹e₁›] [Logic| ‹v₁› > ‹e₂›]
    | gt {v₁ v₂: Nat}: LogicEval₁ s [Logic| ‹num:v₁› > ‹num:v₂›] [Logic| ‹‹v₁ > v₂››]
    | notTrue: LogicEval₁ s [Logic| ! tru] [Logic| fls]
    | notFalse: LogicEval₁ s [Logic| ! fls] [Logic| tru]
    | not {b₁ b₂: Logic} (h₁: LogicEval₁ s b₁ b₂): LogicEval₁ s [Logic| ‹b₁›] [Logic| ‹b₂›]
    | andL {b₁ b₂ b₃: Logic} (h₁: LogicEval₁ s b₁ b₂): LogicEval₁ s [Logic| ‹b₁› && ‹b₃›] [Logic| ‹b₂› && ‹b₃›]
    | andR {v₁ b₁ b₂: Logic} (h₁: LogicValue v₁) (h₂: LogicEval₁ s b₁ b₂): LogicEval₁ s [Logic| ‹v₁› && ‹b₁›] [Logic| ‹v₁› && ‹b₂›]
    | and {v₁ v₂: Bool}: LogicEval₁ s [Logic| ‹‹v₁›› && ‹‹v₂››] [Logic| ‹‹v₁ && v₂››]

  inductive CommandEval₁: (Command × State) → (Command × State) → Prop where
    | assignStep {s: State} {id: String} {e₁ e₂: Arith} (h₁: ArithEval₁ s e₁ e₂): CommandEval₁ ([Imp| ‹id› := ‹e₁›], s) ([Imp| ‹id› := ‹e₂›], s)
    | assign {s: State} {id: String} {n: Nat}: CommandEval₁ ([Imp| ‹id› := ‹num:n›], s) ([Imp| skip], s.update id n)
    | seqStep {s₁ s₂: State} {c₁ c₂ c₃: Command} (h₁: CommandEval₁ (c₁, s₁) (c₂, s₂)): CommandEval₁ ([Imp| ‹c₁›; ‹c₃›], s₁) ([Imp| ‹c₂›; ‹c₃›], s₂)
    | seq {s: State} {c: Command}: CommandEval₁ ([Imp| skip; ‹c›], s) ([Imp| ‹c›], s)
    | iteStep {s: State} {c₁ c₂: Logic} {t f: Command} (h₁: LogicEval₁ s c₁ c₂): CommandEval₁ ([Imp| ite (‹c₁›) { ‹t› } else { ‹f› }], s) ([Imp| ite (‹c₂›) { ‹t› } else { ‹f› }], s)
    | iteTrue {s: State} {t f: Command}: CommandEval₁ ([Imp| ite (tru) { ‹t› } else { ‹f› }], s) ([Imp| ‹t›], s)
    | iteFalse {s: State} {t f: Command}: CommandEval₁ ([Imp| ite (fls) { ‹t› } else { ‹f› }], s) ([Imp| ‹f›], s)
    | while {s: State} {c: Logic} {b: Command}: CommandEval₁ ([Imp| while (‹c›) { ‹b› }], s) ([Imp| ite (‹c›) { ‹b›; while (‹c›) { ‹b› } } else { skip }], s)

  /-
  ## Concurrent Imp
  -/

  namespace ConcurrentImp
    inductive Command: Type where
      | skip: Command
      | assign (id: String) (e: Arith): Command
      | seq (c₁ c₂: Command): Command
      | if (c: Logic) (t f: Command): Command
      | while (c: Logic) (b: Command): Command
      | parallel (c₁ c₂: Command): Command

    declare_syntax_cat concurrent

    syntax:50 "skip" : concurrent
    syntax:50 ident ":=" arith : concurrent
    syntax:50 "‹" term "›" ":=" arith : concurrent
    syntax:40 concurrent ";" concurrent : concurrent
    syntax:50 "ite" "(" logic ")" "{" concurrent "}" "else" "{" concurrent "}" : concurrent
    syntax:50 "while" "(" logic ")" "{" concurrent "}" : concurrent
    syntax:40 concurrent "||" concurrent : concurrent
    syntax "(" concurrent ")" : concurrent
    syntax "‹" term "›" : concurrent

    syntax "[Concurrent|" concurrent "]" : term

    macro_rules
      | `([Concurrent| skip])                                => `(Command.skip)
      | `([Concurrent| $id:ident := $e:arith])               => `(Command.assign $(Lean.quote (toString id.getId)) [Arith| $e])
      | `([Concurrent| ‹$t:term› := $e:arith])               => `(Command.assign $(Lean.quote t) [Arith| $e])
      | `([Concurrent| $x; $y])                              => `(Command.seq [Concurrent| $x] [Concurrent| $y])
      | `([Concurrent| ite ( $c:logic ) { $t } else { $f }]) => `(Command.if [Logic| $c] [Concurrent| $t] [Concurrent| $f])
      | `([Concurrent| while ( $c:logic ) { $b }])           => `(Command.while [Logic| $c] [Concurrent| $b])
      | `([Concurrent| $c₁ || $c₂])                          => `(Command.parallel [Concurrent| $c₁] [Concurrent| $c₂])
      | `([Concurrent| ( $c )])                              => `([Concurrent| $c])
      | `([Concurrent| ‹$t:term› ])                          => pure t

    inductive CommandEval₁: (Command × State) → (Command × State) → Prop where
      | assignStep {s: State} {id: String} {e₁ e₂: Arith} (h₁: ArithEval₁ s e₁ e₂): CommandEval₁ ([Concurrent| ‹id› := ‹e₁›], s) ([Concurrent| ‹id› := ‹e₂›], s)
      | assign {s: State} {id: String} {n: Nat}: CommandEval₁ ([Concurrent| ‹id› := ‹num:n›], s) ([Concurrent| skip], s.update id n)
      | seqStep {s₁ s₂: State} {c₁ c₂ c₃: Command} (h₁: CommandEval₁ (c₁, s₁) (c₂, s₂)): CommandEval₁ ([Concurrent| ‹c₁›; ‹c₃›], s₁) ([Concurrent| ‹c₂›; ‹c₃›], s₂)
      | seq {s: State} {c: Command}: CommandEval₁ ([Concurrent| skip; ‹c›], s) ([Concurrent| ‹c›], s)
      | iteStep {s: State} {c₁ c₂: Logic} {t f: Command} (h₁: LogicEval₁ s c₁ c₂): CommandEval₁ ([Concurrent| ite (‹c₁›) { ‹t› } else { ‹f› }], s) ([Concurrent| ite (‹c₂›) { ‹t› } else { ‹f› }], s)
      | iteTrue {s: State} {t f: Command}: CommandEval₁ ([Concurrent| ite (tru) { ‹t› } else { ‹f› }], s) ([Concurrent| ‹t›], s)
      | iteFalse {s: State} {t f: Command}: CommandEval₁ ([Concurrent| ite (fls) { ‹t› } else { ‹f› }], s) ([Concurrent| ‹f›], s)
      | while {s: State} {c: Logic} {b: Command}: CommandEval₁ ([Concurrent| while (‹c›) { ‹b› }], s) ([Concurrent| ite (‹c›) { ‹b›; while (‹c›) { ‹b› } } else { skip }], s)
      | parallelL {s₁ s₂: State} {c₁ c₂ c₃: Command} (h₁: CommandEval₁ (c₁, s₁) (c₂, s₂)): CommandEval₁ ([Concurrent| ‹c₁› || ‹c₃›], s₁) ([Concurrent| ‹c₂› || ‹c₃›], s₂)
      | parallelR {s₁ s₂: State} {c₁ c₂ c₃: Command} (h₁: CommandEval₁ (c₁, s₁) (c₂, s₂)): CommandEval₁ ([Concurrent| ‹c₃› || ‹c₁›], s₁) ([Concurrent| ‹c₃› || ‹c₂›], s₂)
      | parallel {s: State}: CommandEval₁ ([Concurrent| skip || skip], s) ([Concurrent| skip], s)

    def parallelLoop := [Concurrent|
      Y := 1 || while (Y = 0) { X := X + 1 }
    ]

    instance: Trans CommandEval₁ CommandEval₁ CommandEval₁ where
      trans hxy hyz := sorry

    infix:50 "⤳" => CommandEval₁

    example: ∃ s: State, CommandEval₁ (parallelLoop, [State|]) ([Concurrent| skip], s) ∧ s "X" = 0 :=
      have hw :=
        calc (parallelLoop, [State|])
          _ ⤳ ([Concurrent| skip || while (Y = 0) { X := X + 1 }],                                           [State| Y = 1]) := .parallelL .assign
          _ ⤳ ([Concurrent| skip || ite (Y = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }], [State| Y = 1]) := .parallelR .while
          _ ⤳ ([Concurrent| skip || ite (1 = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }], [State| Y = 1]) := .parallelR (.iteStep (.eqL .ident))
          _ ⤳ ([Concurrent| skip || ite (fls) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }],   [State| Y = 1]) := .parallelR (.iteStep .eq)
          _ ⤳ ([Concurrent| skip || skip],                                                                   [State| Y = 1]) := .parallelR .iteFalse
          _ ⤳ ([Concurrent| skip],                                                                           [State| Y = 1]) := .parallel
      ⟨[State| Y = 1], ⟨hw, rfl⟩⟩

    example: ∃ s: State, CommandEval₁ (parallelLoop, [State|]) ([Concurrent| skip], s) ∧ s "X" = 2 :=
      have hw :=
        calc (parallelLoop, [State|])
          _ ⤳ ([Concurrent| Y := 1 || ite (Y = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }], [State|])                     := .parallelR .while
          _ ⤳ ([Concurrent| Y := 1 || ite (0 = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }], [State|])                     := .parallelR (.iteStep (.eqL .ident))
          _ ⤳ ([Concurrent| Y := 1 || ite (tru) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }],   [State|])                     := .parallelR (.iteStep .eq)
          _ ⤳ ([Concurrent| Y := 1 || X := X + 1; while (Y = 0) { X := X + 1 }],                               [State|])                     := .parallelR .iteTrue
          _ ⤳ ([Concurrent| Y := 1 || X := 0 + 1; while (Y = 0) { X := X + 1 }],                               [State|])                     := .parallelR (.seqStep (.assignStep (.plusL .ident)))
          _ ⤳ ([Concurrent| Y := 1 || X := 1; while (Y = 0) { X := X + 1 }],                                   [State|])                     := .parallelR (.seqStep (.assignStep .plus))
          _ ⤳ ([Concurrent| Y := 1 || skip; while (Y = 0) { X := X + 1 }],                                     [State| X = 1])               := .parallelR (.seqStep .assign)
          _ ⤳ ([Concurrent| Y := 1 || while (Y = 0) { X := X + 1 }],                                           [State| X = 1])               := .parallelR .seq
          _ ⤳ ([Concurrent| Y := 1 || ite (Y = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }], [State| X = 1])               := .parallelR .while
          _ ⤳ ([Concurrent| Y := 1 || ite (0 = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }], [State| X = 1])               := .parallelR (.iteStep (.eqL .ident))
          _ ⤳ ([Concurrent| skip || ite (0 = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }],   [State| X = 1, Y = 1])        := .parallelL .assign
          _ ⤳ ([Concurrent| skip || ite (tru) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }],     [State| X = 1, Y = 1])        := .parallelR (.iteStep .eq)
          _ ⤳ ([Concurrent| skip || X := X + 1; while (Y = 0) { X := X + 1 }],                                 [State| X = 1, Y = 1])        := .parallelR .iteTrue
          _ ⤳ ([Concurrent| skip || X := 1 + 1; while (Y = 0) { X := X + 1 }],                                 [State| X = 1, Y = 1])        := .parallelR (.seqStep (.assignStep (.plusL .ident)))
          _ ⤳ ([Concurrent| skip || X := 2; while (Y = 0) { X := X + 1 }],                                     [State| X = 1, Y = 1])        := .parallelR (.seqStep (.assignStep .plus))
          _ ⤳ ([Concurrent| skip || skip; while (Y = 0) { X := X + 1 }],                                       [State| X = 1, Y = 1, X = 2]) := .parallelR (.seqStep .assign)
          _ ⤳ ([Concurrent| skip || while (Y = 0) { X := X + 1 }],                                             [State| X = 1, Y = 1, X = 2]) := .parallelR .seq
          _ ⤳ ([Concurrent| skip || ite (Y = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }],   [State| X = 1, Y = 1, X = 2]) := .parallelR .while
          _ ⤳ ([Concurrent| skip || ite (1 = 0) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }],   [State| X = 1, Y = 1, X = 2]) := .parallelR (.iteStep (.eqL .ident))
          _ ⤳ ([Concurrent| skip || ite (fls) { X := X + 1; while (Y = 0) { X := X + 1 } } else { skip }],     [State| X = 1, Y = 1, X = 2]) := .parallelR (.iteStep .eq)
          _ ⤳ ([Concurrent| skip || skip],                                                                     [State| X = 1, Y = 1, X = 2]) := .parallelR .iteFalse
          _ ⤳ ([Concurrent| skip],                                                                             [State| X = 1, Y = 1, X = 2]) := .parallel
      ⟨[State| X = 1, Y = 1, X = 2], ⟨hw, rfl⟩⟩

    namespace Term
      theorem parallelLoop.any: ∀ n: Nat, ∃ s: State, CommandEval₁ (parallelLoop, [State|]) ([Concurrent| skip], s) ∧ s "X" = n
        | .zero => sorry
        | .succ n => sorry
    end Term

    namespace Tactic
      theorem parallelLoop.any (n: Nat): ∃ s: State, CommandEval₁ (parallelLoop, [State|]) ([Concurrent| skip], s) ∧ s "X" = n := by
        cases n with
          | zero => sorry
          | succ n => sorry
    end Tactic

    namespace Blended
      theorem parallelLoop.any: ∀ n: Nat, ∃ s: State, CommandEval₁ (parallelLoop, [State|]) ([Concurrent| skip], s) ∧ s "X" = n
        | .zero => sorry
        | .succ n => sorry
    end Blended
  end ConcurrentImp

  /-
  ## A Small-Step Stack Machine
  -/

  abbrev Stack := _root_.SoftwareFoundations.LogicalFoundations.Imp.Stack
  abbrev Program := _root_.SoftwareFoundations.LogicalFoundations.Imp.Program

  inductive ProgramEval₁ (s: State): (Program × Stack) → (Program × Stack) → Prop where
    | push {stk: Stack} {n: Nat} {p: Program}: ProgramEval₁ s (.push n :: p, stk) (p, n :: stk)
    | load {stk: Stack} {id: String} {p: Program}: ProgramEval₁ s (.load id :: p, stk) (p, s id :: stk)
    | plus {stk: Stack} {n₁ n₂: Nat} {p: Program}: ProgramEval₁ s (.plus :: p, n₂ :: n₁ :: stk) (p, (n₁ + n₂) :: stk)
    | minus {stk: Stack} {n₁ n₂: Nat} {p: Program}: ProgramEval₁ s (.plus :: p, n₂ :: n₁ :: stk) (p, (n₁ - n₂) :: stk)
    | mult {stk: Stack} {n₁ n₂: Nat} {p: Program}: ProgramEval₁ s (.plus :: p, n₂ :: n₁ :: stk) (p, (n₁ * n₂) :: stk)

  def ProgramEval (s: State) := MultiStep (ProgramEval₁ s)

  namespace Term
    theorem Arith.compile.correct: True := sorry
  end Term

  namespace Tactic
    theorem Arith.compile.correct: True := by sorry
  end Tactic

  namespace Blended
    theorem Arith.compile.correct: True := sorry
  end Blended

  /-
  ## Aside: A `normalize` Tactic
  -/

  -- TODO: Tactics in Lean
end SoftwareFoundations.ProgrammingLanguageFoundations.SmallStep
