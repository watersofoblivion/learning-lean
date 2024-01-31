/-
# Small-Step Operational Semantics
-/

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
          calc Term.plus (.const _) _
            _ = Term.plus (.const _) _ := congrArg (Term.plus (.const _)) ih
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
      | _, _, _, .plusR hv h₁, .plusL h₂ =>
        sorry
      | _, _, _, .plusR hv₁ h₁, .plusR hv₂ h₂ =>
        have ih := deterministic h₁ h₂
        -- calc Term.plus (.const _) _
        --   _ = Term.plus (.const _) _ := congrArg (Term.plus (.const _)) ih
        sorry
  end Term

  namespace Tactic
    theorem Eval₁.deterministic: Relation.deterministic Eval₁ := by
      intro _ _ _
      intro h₁ h₂
      cases h₁ <;> cases h₂ <;> try (first | rfl
                                           | contradiction)
      case plusL.plusL _ _ _ h₁ _ h₂       => rw [deterministic h₁ h₂]
      case plusR.plusR _ _ hv₁ h₁ _ hv₂ h₂ => rw [deterministic h₁ h₂]
      case plusL.plusR _ _ _ h₁ _ hv h₂    => sorry
      case plusR.plusL _ _ _ hv h₁ _ h₂    => sorry
  end Tactic

  namespace Blended
    theorem Eval₁.deterministic: Relation.deterministic Eval₁
      | _, _, _, .constConst, .constConst => by rfl
      | _, _, _, .plusL h₁, .plusL h₂ => by rw [deterministic h₁ h₂]
      | _, _, _, .plusR hv₁ h₁, .plusR hv₂ h₂ => by rw [deterministic h₁ h₂]
      | _, _, _, .plusR hv h₁, .plusL h₂ => sorry
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
              · apply Exists.intro
                · apply Eval₁.plusL
                  · sorry
                  · sorry
            | inl hv₁ =>
              cases ih₂ with
                | inr ex =>
                  apply Or.inr
                  · apply Exists.intro
                    · apply Eval₁.plusR
                      · exact hv₁
                      · sorry
                      · sorry
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
          match strong_progress c, strong_progress t, strong_progress f with
            | .inl .true, _, _ => .inr ⟨[TF| ‹t›], .testTrue⟩
            | .inl .false, _, _ => .inr ⟨[TF| ‹f›], .testFalse⟩
            | .inr ⟨w, hw⟩, _, _ => .inr ⟨[TF| test (‹w›) { ‹t›} else { ‹f› }], .test hw⟩

      theorem Eval₁.deterministic: Relation.deterministic Eval₁
        | _, _, _, .testTrue, .testTrue
        | _, _, _, .testFalse, .testFalse => rfl
        | _, _, _, .test h₁, .test h₂ =>
          have ih := deterministic h₁ h₂
          calc Term.test _ _ _
            _ = Term.test _ _ _ := by rw [ih] -- TODO: Remove Tactic Block
    end Term

    namespace Tactic
      theorem Eval₁.strong_progress: ∀ t₁: Term, Value t₁ ∨ ∃ t₂: Term, Eval₁ t₁ t₂ := sorry

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
          match strong_progress c, strong_progress t, strong_progress f with
            | .inl .true, _, _ => .inr ⟨[TF| ‹t›], .testTrue⟩
            | .inl .false, _, _ => .inr ⟨[TF| ‹f›], .testFalse⟩
            | .inr ⟨w, hw⟩, _, _ => .inr ⟨[TF| test (‹w›) { ‹t›} else { ‹f› }], .test hw⟩

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
        | shortCircuit {c t₁ t₂ f₁ f₂} (h₁: Eval t₁ t₂) (h₂: Eval f₁ f₂) (h₃: t₂ = f₂): Eval₁ [TF| test (‹c›) { ‹t₁› } else { ‹f₁› }] t₁

      notation t₁ "⟶" t₂ => Eval₁ t₁ t₂

      -- TODO
    end Temp5
  end Temp4

  /-
  ## Multi-Step Reduction
  -/


end SoftwareFoundations.ProgrammingLanguageFoundations.SmallStep
