/-
# Program Equivalence
-/

import Mathlib.tactic.linarith

import «SoftwareFoundations».«LogicalFoundations».«Maps»
import «SoftwareFoundations».«LogicalFoundations».«Imp»

namespace SoftwareFoundations.ProgrammingLanguageFoundations.Equiv
  open SoftwareFoundations.LogicalFoundations.Imp

  /-
  ## Behavioral Equivalence
  -/

  /-
  ### Definitions
  -/

  @[reducible] def _root_.SoftwareFoundations.LogicalFoundations.Imp.Arith.equiv (a₁ a₂: Arith): Prop := ∀ s: State, a₁.eval s = a₂.eval s
  @[reducible] def _root_.SoftwareFoundations.LogicalFoundations.Imp.Logic.equiv (l₁ l₂: Logic): Prop := ∀ s: State, l₁.eval s = l₂.eval s

  @[reducible] def _root_.SoftwareFoundations.LogicalFoundations.Imp.Command.equiv (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, CommandEval c₁ s₁ s₂ ↔ CommandEval c₂ s₁ s₂
  @[reducible] def _root_.SoftwareFoundations.LogicalFoundations.Imp.Command.refines (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, CommandEval c₁ s₁ s₂ → CommandEval c₂ s₁ s₂

  infix:50 "≈" => Arith.equiv
  infix:50 "≈" => Logic.equiv
  infix:50 "≈" => Command.equiv

  namespace Term
    example: [Arith| X - X] ≈ [Arith| 0] :=
      fun s =>
        calc [Arith| X - X].eval s
          _ = (s "X") - (s "X") := rfl
          _ = 0                 := Nat.sub_self (s "X")
          _ = [Arith| 0].eval s := rfl

    example: [Logic| (X - X) = 0] ≈ [Logic| tru] :=
      fun s =>
        calc [Logic| (X - X) = 0].eval s
          _ = BEq.beq ((s "X") - (s "X")) 0 := rfl
          _ = BEq.beq 0 0                   := congrFun (congrArg BEq.beq (Nat.sub_self (s "X"))) 0
          _ = [Logic| tru].eval s           := rfl
  end Term

  namespace Tactic
    example: [Arith| X - X] ≈ [Arith| 0] := by
      unfold Arith.equiv
      intro s
      simp

    example: [Logic| (X - X) = 0] ≈ [Logic| tru] := by
      unfold Logic.equiv
      intro s
      simp
  end Tactic

  namespace Blended
    example: [Arith| X - X] ≈ [Arith| 0] :=
      fun s =>
        calc [Arith| X - X].eval s
          _ = (s "X") - (s "X") := by rfl
          _ = 0                 := by rw [Nat.sub_self]
          _ = [Arith| 0].eval s := by rfl


    example: [Logic| (X - X) = 0] ≈ [Logic| tru] :=
      fun s =>
        calc [Logic| (X - X) = 0].eval s
          _ = BEq.beq ((s "X") - (s "X")) 0 := by rfl
          _ = BEq.beq 0 0                   := by rw [Nat.sub_self]
          _ = [Logic| tru].eval s           := by rfl
  end Blended

  /-
  ### Simple Examples
  -/

  private def _root_.SoftwareFoundations.LogicalFoundations.Imp.Logic.trueFalse {s: State} (b: Logic) (h₁: b.eval s = true) (h₂: b.eval s = false): α :=
    False.elim (by simp_all)

  namespace Term
    theorem Command.skip_left {c: Command}: [Imp| skip; ‹c›] ≈ c
      | _, _ =>
        have mp
          | .seq _ _ _ (.skip _) h₂ => h₂
        have mpr
          | .skip _                   => .seq _ _ _ (.skip _) (.skip _)
          | .assign _ h               => .seq _ _ _ (.skip _) (.assign _ h)
          | .seq _ _ _ h₁ h₂          => .seq _ _ _ (.skip _) (.seq _ _ _ h₁ h₂)
          | .ifTrue _ _ h₁ h₂         => .seq _ _ _ (.skip _) (.ifTrue _ _ h₁ h₂)
          | .ifFalse _ _ h₁ h₂        => .seq _ _ _ (.skip _) (.ifFalse _ _ h₁ h₂)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .seq _ _ _ (.skip _) (.whileTrue _ _ _ h₁ h₂ h₃)
          | .whileFalse _ h₁          => .seq _ _ _ (.skip _) (.whileFalse _ h₁)
        ⟨mp, mpr⟩

    theorem Command.skip_right {c: Command}: [Imp| ‹c›; skip] ≈ c
      | _, _ =>
        have mp
          | .seq _ _ _ h₁ (.skip _) => h₁
        have mpr
          | .skip _                   => .seq _ _ _ (.skip _) (.skip _)
          | .assign _ h               => .seq _ _ _ (.assign _ h) (.skip _)
          | .seq _ _ _ h₁ h₂          => .seq _ _ _ (.seq _ _ _ h₁ h₂) (.skip _)
          | .ifTrue _ _ h₁ h₂         => .seq _ _ _ (.ifTrue _ _ h₁ h₂) (.skip _)
          | .ifFalse _ _ h₁ h₂        => .seq _ _ _ (.ifFalse _ _ h₁ h₂) (.skip _)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .seq _ _ _ (.whileTrue _ _ _ h₁ h₂ h₃) (.skip _)
          | .whileFalse _ h₁          => .seq _ _ _ (.whileFalse _ h₁) (.skip _)
        ⟨mp, mpr⟩

    example {t f: Command}: [Imp| ite (tru) { ‹t› } else { ‹f› }] ≈ t
      | _, _ =>
        have mp
          | .ifTrue _ _ _ h₂ => h₂
          | .ifFalse _ _ h₁ _ => Logic.true.trueFalse rfl h₁
        have mpr
          | .skip _                   => .ifTrue _ _ rfl (.skip _)
          | .assign _ h               => .ifTrue _ _ rfl (.assign _ h)
          | .seq _ _ _ h₁ h₂          => .ifTrue _ _ rfl (.seq _ _ _ h₁ h₂)
          | .ifTrue _ _ h₁ h₂         => .ifTrue _ _ rfl (.ifTrue _ _ h₁ h₂)
          | .ifFalse _ _ h₁ h₂        => .ifTrue _ _ rfl (.ifFalse _ _ h₁ h₂)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .ifTrue _ _ rfl (.whileTrue _ _ _ h₁ h₂ h₃)
          | .whileFalse _ h           => .ifTrue _ _ rfl (.whileFalse _ h)
        ⟨mp, mpr⟩

    theorem Command.if_true {b: Logic} {c₁ c₂: Command} (h: b ≈ .true): [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ c₁
      | _, _ =>
        have truu: b.eval _ = Logic.true.eval _ := h _
        have mp
          | .ifTrue _ _ _ h₂ => h₂
          | .ifFalse _ _ h₁ _ => b.trueFalse truu h₁
        have mpr
          | .skip _                   => .ifTrue _ _ truu (.skip _)
          | .assign _ h₁              => .ifTrue _ _ truu (.assign _ h₁)
          | .seq _ _ _ h₁ h₂          => .ifTrue _ _ truu (.seq _ _ _ h₁ h₂)
          | .ifTrue _ _ h₁ h₂         => .ifTrue _ _ truu (.ifTrue _ _ h₁ h₂)
          | .ifFalse _ _ h₁ h₂        => .ifTrue _ _ truu (.ifFalse _ _ h₁ h₂)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .ifTrue _ _ truu (.whileTrue _ _ _ h₁ h₂ h₃)
          | .whileFalse _ h₁          => .ifTrue _ _ truu (.whileFalse _ h₁)
        ⟨mp, mpr⟩

    theorem Command.if_false {b: Logic} {c₁ c₂: Command} (h: b ≈ .false): [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ c₂
      | _, _ =>
        have falz: b.eval _ = Logic.false.eval _ := h _
        have mp
          | .ifTrue _ _ h₁ _ => b.trueFalse h₁ falz
          | .ifFalse _ _ _ h₂ => h₂
        have mpr
          | .skip _                   => .ifFalse _ _ falz (.skip _)
          | .assign _ h₁              => .ifFalse _ _ falz (.assign _ h₁)
          | .seq _ _ _ h₁ h₂          => .ifFalse _ _ falz (.seq _ _ _ h₁ h₂)
          | .ifTrue _ _ h₁ h₂         => .ifFalse _ _ falz (.ifTrue _ _ h₁ h₂)
          | .ifFalse _ _ h₁ h₂        => .ifFalse _ _ falz (.ifFalse _ _ h₁ h₂)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .ifFalse _ _ falz (.whileTrue _ _ _ h₁ h₂ h₃)
          | .whileFalse _ h₁          => .ifFalse _ _ falz (.whileFalse _ h₁)
        ⟨mp, mpr⟩

    theorem Command.if_swap {b: Logic} {c₁ c₂: Command}: [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ [Imp| ite ( ! ‹b› ) { ‹c₂› } else { ‹c₁› }]
      | _, _ =>
        have mp := sorry
        have mpr := sorry
        ⟨mp, mpr⟩

    theorem Command.while_false {c: Logic} {b: Command} (h: c ≈ .false): [Imp| while (‹c›) { ‹b› }] ≈ [Imp| skip]
      | _, _ =>
        have falz: c.eval _ = Logic.false.eval _ := h _
        have mp
          | .whileTrue _ _ _ h₁ _ _=> c.trueFalse h₁ falz
          | .whileFalse _ _ => .skip _
        have mpr
          | .skip _ => .whileFalse _ falz
        ⟨mp, mpr⟩

    theorem Command.while_true {c: Logic} {b: Command} (h: c ≈ .true): [Imp| while (‹c›) { ‹b› }] ≈ [Imp| while (tru) { skip }]
      | _, _ =>
        have truu: c.eval _ = Logic.true.eval _ := h _
        have hh: Logic.true.equiv .true
          | _ => rfl
        have mp
          | .whileTrue _ _ _ h₁ h₂ h₃ => absurd (CommandEval.whileTrue _ _ _ h₁ h₂ h₃) (nonterm h)
          | .whileFalse _ h₁ => c.trueFalse truu h₁
        have mpr
          | .whileTrue _ _ _ h₁ h₂ h₃ => absurd (CommandEval.whileTrue _ _ _ h₁ h₂ h₃) (nonterm hh)
          | .whileFalse _ h₁ => Logic.true.trueFalse rfl h₁
        ⟨mp, mpr⟩
      where
        nonterm {c: Logic} {b: Command} {s₁ s₂: State} (h: c ≈ .true): ¬(s₁ =[[Imp| while (‹c›) { ‹b› }]]=> s₂)
          | .whileTrue s₁ s₂ s₃ h₁ h₂ h₃ =>
            sorry
          | .whileFalse _ h₁ => c.trueFalse (h _) h₁

    theorem Command.loop_unrolling {c: Logic} {b: Command}: [Imp| while (‹c›) { ‹b› }] ≈ [Imp| ite (‹c›) { ‹b›; while (‹c›) { ‹b› }} else { skip }]
      | _, _ =>
        have mp
          | .whileTrue _ _ _ h₁ h₂ h₃ => .ifTrue _ _ h₁ (.seq _ _ _ h₂ h₃)
          | .whileFalse _ h₁ => .ifFalse _ _ h₁ (.skip _)
        have mpr
          | .ifTrue _ _ h₁ (.seq _ _ _ h₂ h₃) => .whileTrue _ _ _ h₁ h₂ h₃
          | .ifFalse _ _ h₁ (.skip _) => .whileFalse _ h₁
        ⟨mp, mpr⟩

    theorem Command.seq_assoc {c₁ c₂ c₃: Command}: [Imp| (‹c₁›; ‹c₂›); ‹c₃›] ≈ [Imp| ‹c₁›; (‹c₂›; ‹c₃›)]
      | _, _ =>
        have mp
          | .seq _ _ _ (.seq _ _ _ h₁ h₂) h₃ => .seq _ _ _ h₁ (.seq _ _ _ h₂ h₃)
        have mpr
          | .seq _ _ _ h₁ (.seq _ _ _ h₂ h₃) => .seq _ _ _ (.seq _ _ _ h₁ h₂) h₃
        ⟨mp, mpr⟩

    theorem Command.identity_assignment {id: String}: [Imp| ‹id› := ‹id:id›] ≈ [Imp| skip]
      | _, _ =>
        -- Should use Maps.TotalMap.updateSame
        have mp
          | .assign _ h => sorry
        have mpr
          | .skip _ => sorry
        ⟨mp, mpr⟩

    theorem Command.assign_arith_equiv {id: String} {e: Arith} (h: [Arith| ‹id:id›] ≈ e): [Imp| skip] ≈ [Imp| ‹id› := ‹e› ]
      | _, _ =>
        have mp
          | .skip _ => sorry
        have mpr
          | .assign _ _ => sorry
        ⟨mp, mpr⟩
  end Term

  namespace Tactic
    @[scoped simp]
    theorem Command.skip_left {c: Command}: [Imp| skip; ‹c›] ≈ c := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .seq _ _ _ h₁ _ => cases h₁; assumption
      · intro h
        cases h
        <;> try (apply CommandEval.seq
                 · apply CommandEval.skip
                 . constructor
                   repeat assumption)
        case ifFalse =>
          apply CommandEval.seq
          · apply CommandEval.skip
          . apply CommandEval.ifFalse
            repeat assumption
        case whileFalse =>
          apply CommandEval.seq
          · apply CommandEval.skip
          · apply CommandEval.whileFalse
            repeat assumption

    @[scoped simp]
    theorem Command.skip_right {c: Command}: [Imp| ‹c›; skip] ≈ c := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .seq _ _ _ _ h₂ => cases h₂; assumption
      · intro h
        cases h
        <;> try (apply CommandEval.seq
                 . constructor
                   repeat assumption
                 · apply CommandEval.skip)
        case ifFalse =>
          apply CommandEval.seq
          . apply CommandEval.ifFalse
            repeat assumption
          · apply CommandEval.skip
        case whileFalse =>
          apply CommandEval.seq
          · apply CommandEval.whileFalse
            repeat assumption
          · apply CommandEval.skip

    example {t f: Command}: [Imp| ite (tru) { ‹t› } else { ‹f› }] ≈ t := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .ifTrue _ _ _ _ => assumption
        | .ifFalse _ _ _ _ => contradiction
      · intro h
        cases h
        <;> try (apply CommandEval.ifTrue
                 · unfold Logic.eval
                   rfl
                 · constructor
                   repeat assumption)
        case ifFalse c t f h₁ h₂ =>
          apply CommandEval.ifTrue
          · rfl
          . apply CommandEval.ifFalse
            repeat assumption
        case whileFalse c b h₁ =>
          apply CommandEval.ifTrue
          · rfl
          . apply CommandEval.whileFalse
            repeat assumption

    @[scoped simp]
    theorem Command.if_true {b: Logic} {c₁ c₂: Command} (h: b ≈ .true): [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ c₁ := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .ifTrue _ _ _ _ => assumption
        | .ifFalse _ _ h₃ _ =>
          rw [h s₁] at h₃
          contradiction
      · intro h
        cases h
        <;> try (apply CommandEval.ifTrue
                 · apply h
                 · constructor
                   repeat assumption)
        case ifFalse =>
          apply CommandEval.ifTrue
          · apply h
          · apply CommandEval.ifFalse
            repeat assumption
        case whileFalse =>
          apply CommandEval.ifTrue
          · apply h
          · apply CommandEval.whileFalse
            repeat assumption

    @[scoped simp]
    theorem Command.if_false {b: Logic} {c₁ c₂: Command} (h: b ≈ .false): [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ c₂ := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .ifTrue _ _ h₁ _ =>
            rw [h s₁] at h₁
            contradiction
        | .ifFalse _ _ _ _ => assumption
      · intro h
        cases h
        <;> try (apply CommandEval.ifFalse
                 · apply h
                 . constructor
                   repeat assumption)
        case ifFalse =>
            apply CommandEval.ifFalse
            · apply h
            . apply CommandEval.ifFalse
              repeat assumption
        case whileFalse =>
            apply CommandEval.ifFalse
            · apply h
            . apply CommandEval.whileFalse
              repeat assumption

    theorem Command.if_swap {b: Logic} {c₁ c₂: Command}: [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ [Imp| ite (!‹b›) { ‹c₂› } else { ‹c₁› }] := by
      intro s₁ s₂
      apply Iff.intro
      · sorry
      · sorry

    @[scoped simp]
    theorem Command.while_false {c: Logic} {b: Command} (h: c ≈ .false): [Imp| while (‹c›) { ‹b› }] ≈ [Imp| skip] := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .whileTrue _ _ _ h₁ _ _ =>
          rw [h s₁] at h₁
          contradiction
        | .whileFalse _ _ => apply CommandEval.skip
      · intro
        | .skip _ =>
            apply CommandEval.whileFalse
            · rw [h s₁]

    @[scoped simp]
    theorem Command.while_true {c: Logic} {b: Command} (h: c ≈ .true): [Imp| while (‹c›) { ‹b› }] ≈ [Imp| while (tru) { skip }] := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .whileTrue _ _ _ h₁ _ h₃ =>
          have := nonterm h h₃
          contradiction
        | .whileFalse _ _ => simp_all
      · intro x
        cases x with
        | whileTrue _ _ _ h₁ h₂ h₃ =>
          have := by
            apply nonterm
            · exact h
            . sorry -- exact h₃
            · sorry
            · sorry
            · sorry
          contradiction
        | whileFalse _ _ => simp_all
      where
        nonterm {c: Logic} {b: Command} {s₁ s₂: State} (h: c ≈ .true): ¬(s₁ =[[Imp| while (‹c›) { ‹b› }]]=> s₂) := by
          intro
          | .whileTrue s₃ s₄ s₅ h₁ h₂ h₃ =>
            -- simp_all
            rw [h] at h₁
            sorry
          | .whileFalse _ _ => simp_all

    theorem Command.loop_unrolling {c: Logic} {b: Command}: [Imp| while (‹c›) { ‹b› }] ≈ [Imp| ite (‹c›) { ‹b›; while (‹c›) { ‹b› }} else { skip }] := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .whileTrue _ _ _ h₁ h₂ h₃ =>
          apply CommandEval.ifTrue
          · exact h₁
          · exact CommandEval.seq _ _ _ h₂ h₃
        | .whileFalse _ h₁ =>
          apply CommandEval.ifFalse
          · exact h₁
          · apply CommandEval.skip
      · intro
        | .ifTrue _ _ h₁ (.seq _ _ _ h₂ h₃) =>
          exact CommandEval.whileTrue _ _ _ h₁ h₂ h₃
          repeat assumption
        | .ifFalse _ _ h₁ (.skip _) =>
          exact CommandEval.whileFalse _ h₁

    theorem Command.seq_assoc {c₁ c₂ c₂: Command}: [Imp| (‹c₁›; ‹c₂›); ‹c₃›] ≈ [Imp| ‹c₁›; (‹c₂›; ‹c₃›)] := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .seq _ _ _ h₁ _ =>
          cases h₁
          · apply CommandEval.seq
            <;> (try apply CommandEval.seq
                 repeat assumption)
      · intro
        | .seq _ _ _ _ h₂ =>
          cases h₂
          · apply CommandEval.seq
            <;> (try apply CommandEval.seq
                 repeat assumption)

    @[scoped simp]
    theorem Command.identity_assignment {id: String}: [Imp| ‹id› := ‹id:id›] ≈ [Imp| skip] := by
      intro s₁ s₂
      apply Iff.intro
      · sorry
      · sorry

    theorem Command.assign_arith_equiv {id: String} {e: Arith} (h: [Arith| ‹id:id›] ≈ e): [Imp| skip] ≈ [Imp| ‹id› := ‹e› ] := by
      unfold Command.equiv
      intro s₁ s₂
      apply Iff.intro
      · sorry
      · sorry
  end Tactic

  namespace Blended
    @[scoped simp]
    theorem Command.skip_left {c: Command}: [Imp| skip; ‹c›] ≈ c
      | _, _ =>
        have mp
          | .seq _ _ _ (.skip _) h₂ => h₂
        have mpr
          | .skip _                   => .seq _ _ _ (.skip _) (.skip _)
          | .assign _ h               => .seq _ _ _ (.skip _) (.assign _ h)
          | .seq _ _ _ h₁ h₂          => .seq _ _ _ (.skip _) (.seq _ _ _ h₁ h₂)
          | .ifTrue _ _ h₁ h₂         => .seq _ _ _ (.skip _) (.ifTrue _ _ h₁ h₂)
          | .ifFalse _ _ h₁ h₂        => .seq _ _ _ (.skip _) (.ifFalse _ _ h₁ h₂)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .seq _ _ _ (.skip _) (.whileTrue _ _ _ h₁ h₂ h₃)
          | .whileFalse _ h₁          => .seq _ _ _ (.skip _) (.whileFalse _ h₁)
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.skip_right {c: Command}: [Imp| ‹c›; skip] ≈ c
      | _, _ =>
        have mp
          | .seq _ _ _ h₁ (.skip _) => h₁
        have mpr
          | .skip _                   => .seq _ _ _ (.skip _) (.skip _)
          | .assign _ h               => .seq _ _ _ (.assign _ h) (.skip _)
          | .seq _ _ _ h₁ h₂          => .seq _ _ _ (.seq _ _ _ h₁ h₂) (.skip _)
          | .ifTrue _ _ h₁ h₂         => .seq _ _ _ (.ifTrue _ _ h₁ h₂) (.skip _)
          | .ifFalse _ _ h₁ h₂        => .seq _ _ _ (.ifFalse _ _ h₁ h₂) (.skip _)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .seq _ _ _ (.whileTrue _ _ _ h₁ h₂ h₃) (.skip _)
          | .whileFalse _ h₁          => .seq _ _ _ (.whileFalse _ h₁) (.skip _)
        ⟨mp, mpr⟩

    @[scoped simp]
    example {t f: Command}: [Imp| ite (tru) { ‹t› } else { ‹f› }] ≈ t
      | _, _ =>
        have mp
          | .ifTrue _ _ _ h₂ => h₂
          | .ifFalse _ _ h₁ _ => Logic.true.trueFalse rfl h₁
        have mpr
          | .skip _                   => .ifTrue _ _ rfl (.skip _)
          | .assign _ h               => .ifTrue _ _ rfl (.assign _ h)
          | .seq _ _ _ h₁ h₂          => .ifTrue _ _ rfl (.seq _ _ _ h₁ h₂)
          | .ifTrue _ _ h₁ h₂         => .ifTrue _ _ rfl (.ifTrue _ _ h₁ h₂)
          | .ifFalse _ _ h₁ h₂        => .ifTrue _ _ rfl (.ifFalse _ _ h₁ h₂)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .ifTrue _ _ rfl (.whileTrue _ _ _ h₁ h₂ h₃)
          | .whileFalse _ h           => .ifTrue _ _ rfl (.whileFalse _ h)
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.if_true {b: Logic} {c₁ c₂: Command} (h: b ≈ .true): [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ c₁
      | _, _ =>
        have truu: b.eval _ = Logic.true.eval _ := h _
        have mp
          | .ifTrue _ _ _ h₂ => h₂
          | .ifFalse _ _ h₁ _ => b.trueFalse truu h₁
        have mpr
          | .skip _                   => .ifTrue _ _ truu (.skip _)
          | .assign _ h₁              => .ifTrue _ _ truu (.assign _ h₁)
          | .seq _ _ _ h₁ h₂          => .ifTrue _ _ truu (.seq _ _ _ h₁ h₂)
          | .ifTrue _ _ h₁ h₂         => .ifTrue _ _ truu (.ifTrue _ _ h₁ h₂)
          | .ifFalse _ _ h₁ h₂        => .ifTrue _ _ truu (.ifFalse _ _ h₁ h₂)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .ifTrue _ _ truu (.whileTrue _ _ _ h₁ h₂ h₃)
          | .whileFalse _ h₁          => .ifTrue _ _ truu (.whileFalse _ h₁)
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.if_false {b: Logic} {c₁ c₂: Command} (h: b ≈ .false): [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ c₂
      | _, _ =>
        have falz: b.eval _ = Logic.false.eval _ := h _
        have mp
          | .ifTrue _ _ h₁ _ => b.trueFalse h₁ falz
          | .ifFalse _ _ _ h₂ => h₂
        have mpr
          | .skip _                   => .ifFalse _ _ falz (.skip _)
          | .assign _ h₁              => .ifFalse _ _ falz (.assign _ h₁)
          | .seq _ _ _ h₁ h₂          => .ifFalse _ _ falz (.seq _ _ _ h₁ h₂)
          | .ifTrue _ _ h₁ h₂         => .ifFalse _ _ falz (.ifTrue _ _ h₁ h₂)
          | .ifFalse _ _ h₁ h₂        => .ifFalse _ _ falz (.ifFalse _ _ h₁ h₂)
          | .whileTrue _ _ _ h₁ h₂ h₃ => .ifFalse _ _ falz (.whileTrue _ _ _ h₁ h₂ h₃)
          | .whileFalse _ h₁          => .ifFalse _ _ falz (.whileFalse _ h₁)
        ⟨mp, mpr⟩

    theorem Command.if_swap {b: Logic} {c₁ c₂: Command}: [Imp| ite (‹b›) { ‹c₁› } else { ‹c₂› }] ≈ [Imp| ite (!‹b›) { ‹c₂› } else { ‹c₁› }] := sorry

    @[scoped simp]
    theorem Command.while_false {c: Logic} {b: Command} (h: c ≈ .false): [Imp| while (‹c›) { ‹b› }] ≈ [Imp| skip]
      | _, _ =>
        have falz: c.eval _ = Logic.false.eval _ := h _
        have mp
          | .whileTrue _ _ _ h₁ _ _=> c.trueFalse h₁ falz
          | .whileFalse _ _ => .skip _
        have mpr
          | .skip _ => .whileFalse _ falz
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.while_true {c: Logic} {b: Command} (h: c ≈ .true): [Imp| while (‹c›) { ‹b› }] ≈ [Imp| while (tru) { skip }]
      | _, _ =>
        have truu: c.eval _ = Logic.true.eval _ := h _
        have hh: Logic.true.equiv .true
          | _ => rfl
        have mp
          | .whileTrue _ _ _ h₁ h₂ h₃ => absurd (CommandEval.whileTrue _ _ _ h₁ h₂ h₃) (nonterm h)
          | .whileFalse _ h₁ => c.trueFalse truu h₁
        have mpr
          | .whileTrue _ _ _ h₁ h₂ h₃ => absurd (CommandEval.whileTrue _ _ _ h₁ h₂ h₃) (nonterm hh)
          | .whileFalse _ h₁ => Logic.true.trueFalse rfl h₁
        ⟨mp, mpr⟩
      where
        nonterm {c: Logic} {b: Command} {s₁ s₂: State} (h: c ≈ .true): ¬(s₁ =[[Imp| while (‹c›) { ‹b› }]]=> s₂)
          | .whileTrue _ _ _ _ _ h₃ => sorry
          | .whileFalse _ h₁ => c.trueFalse (h _) h₁

    theorem Command.loop_unrolling {c: Logic} {b: Command}: [Imp| while (‹c›) { ‹b› }] ≈ [Imp| ite (‹c›) { ‹b›; while (‹c›) { ‹b› }} else { skip }]
      | _, _ =>
        have mp
          | .whileTrue _ _ _ h₁ h₂ h₃ => .ifTrue _ _ h₁ (.seq _ _ _ h₂ h₃)
          | .whileFalse _ h₁ => .ifFalse _ _ h₁ (.skip _)
        have mpr
          | .ifTrue _ _ h₁ (.seq _ _ _ h₂ h₃) => .whileTrue _ _ _ h₁ h₂ h₃
          | .ifFalse _ _ h₁ (.skip _) => .whileFalse _ h₁
        ⟨mp, mpr⟩

    theorem Command.seq_assoc {c₁ c₂ c₃: Command}: [Imp| (‹c₁›; ‹c₂›); ‹c₃›] ≈ [Imp| ‹c₁›; (‹c₂›; ‹c₃›)]
      | _, _ =>
        have mp
          | .seq _ _ _ (.seq _ _ _ h₁ h₂) h₃ => .seq _ _ _ h₁ (.seq _ _ _ h₂ h₃)
        have mpr
          | .seq _ _ _ h₁ (.seq _ _ _ h₂ h₃) => .seq _ _ _ (.seq _ _ _ h₁ h₂) h₃
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.identity_assignment {id: String}: [Imp| ‹id› := ‹id:id›] ≈ [Imp| skip] := by sorry

    theorem Command.assign_arith_equiv {id: String} {e: Arith} (h: [Arith| ‹id:id›] ≈ e): [Imp| skip] ≈ [Imp| ‹id› := ‹e› ] := by sorry
  end Blended

  section
    -- Diverges: X starts > 1 and only increases.
    private def a := [Imp|
      while (X > 0) {
        X := X + 1
      }
    ]

    -- Terminates:
    -- If X == 0, then X := 0, Y := 0
    -- If X != 0, then X := X, Y := 0
    -- In both cases, X retains its value and Y := 0
    private def b := [Imp|
      ite (X = 0) {
        X := X + 1;
        Y := 1
      } else {
        Y := 0
      };
      X := X - Y;
      Y := 0
    ]

    -- Terminates, no-op
    private def c := [Imp|
      skip
    ]

    -- Diverges: X is positive (Nat ≠ 0). X * positive is ≥ 0, + 1 > 0.
    private def d := [Imp|
      while (X ≠ 0) {
        X := X * Y + 1
      }
    ]

    -- After termination, Y := 0 and, implicitly, X := X
    private def e := [Imp|
      Y := 0
    ]

    -- Diverges: Y := X + 1, so X != Y.  In the loop, assigns the same, so loop
    -- never terminates.
    private def f := [Imp|
      Y := X + 1;
      while (X ≠ Y) {
        Y := X + 1
      }
    ]

    -- Diverges: Canonical example
    private def g := [Imp|
      while (tru) {
        skip
      }
    ]

    -- No-op.  X always equals X, so is "while false"
    private def h := [Imp|
      while (X ≠ X) {
        X := X + 1
      }
    ]

    -- May diverge:
    -- * If X = Y, terminates.
    -- * If X != Y, X will never equal Y.
    private def i := [Imp|
      while (X ≠ Y) {
        X := Y + 1
      }
    ]

    private def equiv_classes := [
      -- Diverges
      [a, d, f, g],
      -- X is retained, Y := 0
      [b, e],
      -- No-op
      [c, h],
      -- May Diverge
      [i]
    ]

    example: a ≈ d
      | _, _ =>
        have mp := sorry
        have mpr := sorry
        ⟨mp, mpr⟩
    example: d ≈ f
      | _, _ =>
        have mp := sorry
        have mpr := sorry
        ⟨mp, mpr⟩
    example: f ≈ g
      | _, _ =>
        have mp := sorry
        have mpr := sorry
        ⟨mp, mpr⟩

    example: b ≈ e
      | _, _ =>
        have mp := sorry
        have mpr := sorry
        ⟨mp, mpr⟩

    example: c ≈ h
      | _, _ =>
        have mp := sorry
        have mpr := sorry
        ⟨mp, mpr⟩

    example: ¬(a ≈ b) := sorry
    example: ¬(a ≈ c) := sorry
    example: ¬(a ≈ i) := sorry
    example: ¬(b ≈ c) := sorry
    example: ¬(b ≈ i) := sorry
    example: ¬(c ≈ i) := sorry

    -- By transitivity (below) this proves the equivalence classes
  end

  /-
  ## Properties of Behavioral Equivalence
  -/

  /-
  ### Behavioral Equivalence is an Equivalence
  -/

  namespace Term
    theorem Arith.equiv.refl {e: Arith}: e ≈ e
      | _ => Eq.refl (e.eval _)
    theorem Arith.equiv.symm {e₁ e₂: Arith} (h: e₁ ≈ e₂): e₂ ≈ e₁
      | _ => Eq.symm (h _)
    theorem Arith.equiv.trans {e₁ e₂ e₃: Arith} (h₁: e₁ ≈ e₂) (h₂: e₂ ≈ e₃): e₁ ≈ e₃
      | _ => Eq.trans (h₁ _) (h₂ _)

    theorem Logic.equiv.refl {b: Logic}: b ≈ b
      | _ => Eq.refl (b.eval _)
    theorem Logic.equiv.symm {b₁ b₂: Logic} (h: b₁ ≈ b₂): b₂ ≈ b₁
      | _ => Eq.symm (h _)
    theorem Logic.equiv.trans {b₁ b₂ b₃: Logic} (h₁: b₁ ≈ b₂) (h₂: b₂ ≈ b₃): b₁ ≈ b₃
      | _ => Eq.trans (h₁ _) (h₂ _)

    theorem Command.equiv.refl {c: Command}: c ≈ c
      | _, _ => Iff.refl (CommandEval c _ _)
    theorem Command.equiv.symm {c₁ c₂: Command} (h: c₁ ≈ c₂): c₂ ≈ c₁
      | _, _ => Iff.symm (h _ _)
    theorem Command.equiv.trans {c₁ c₂ c₃: Command} (h₁: c₁ ≈ c₂) (h₂: c₂ ≈ c₃): c₁ ≈ c₃
      | _, _ => Iff.trans (h₁ _ _) (h₂ _ _)
  end Term

  namespace Tactic
    theorem Arith.equiv.refl {e: Arith}: e ≈ e := by
      intro
      rfl
    theorem Arith.equiv.symm {e₁ e₂: Arith} (h: e₁ ≈ e₂): e₂ ≈ e₁ := by
      intro
      rw [h _]
    theorem Arith.equiv.trans {e₁ e₂ e₃: Arith} (h₁: e₁ ≈ e₂) (h₂: e₂ ≈ e₃): e₁ ≈ e₃ := by
      intro
      rw [h₁ _, h₂ _]

    theorem Logic.equiv.refl {b: Logic}: b ≈ b := by
      intro
      rfl
    theorem Logic.equiv.symm {b₁ b₂: Logic} (h: b₁ ≈ b₂): b₂ ≈ b₁ := by
      intro
      rw [h _]
    theorem Logic.equiv.trans {b₁ b₂ b₃: Logic} (h₁: b₁ ≈ b₂) (h₂: b₂ ≈ b₃): b₁ ≈ b₃ := by
      intro
      rw [h₁ _, h₂ _]

    theorem Command.equiv.refl {c: Command}: c ≈ c := by
      intro _ _
      rfl
    theorem Command.equiv.symm {c₁ c₂: Command} (h: c₁ ≈ c₂): c₂ ≈ c₁ := by
      intro _ _
      rw [h _ _]
    theorem Command.equiv.trans {c₁ c₂ c₃: Command} (h₁: c₁ ≈ c₂) (h₂: c₂ ≈ c₃): c₁ ≈ c₃ := by
      intro _ _
      rw [h₁ _ _, h₂ _ _]
  end Tactic

  namespace Blended
    theorem Arith.equiv.refl {e: Arith}: e ≈ e
      | _ => Eq.refl (e.eval _)
    theorem Arith.equiv.symm {e₁ e₂: Arith} (h: e₁ ≈ e₂): e₂ ≈ e₁
      | _ => Eq.symm (h _)
    theorem Arith.equiv.trans {e₁ e₂ e₃: Arith} (h₁: e₁ ≈ e₂) (h₂: e₂ ≈ e₃): e₁ ≈ e₃
      | _ => Eq.trans (h₁ _) (h₂ _)

    theorem Logic.equiv.refl {b: Logic}: b ≈ b
      | _ => Eq.refl (b.eval _)
    theorem Logic.equiv.symm {b₁ b₂: Logic} (h: b₁ ≈ b₂): b₂ ≈ b₁
      | _ => Eq.symm (h _)
    theorem Logic.equiv.trans {b₁ b₂ b₃: Logic} (h₁: b₁ ≈ b₂) (h₂: b₂ ≈ b₃): b₁ ≈ b₃
      | _ => Eq.trans (h₁ _) (h₂ _)

    theorem Command.equiv.refl {c: Command}: c ≈ c
      | _, _ => Iff.refl (CommandEval c _ _)
    theorem Command.equiv.symm {c₁ c₂: Command} (h: c₁ ≈ c₂): c₂ ≈ c₁
      | _, _ => Iff.symm (h _ _)
    theorem Command.equiv.trans {c₁ c₂ c₃: Command} (h₁: c₁ ≈ c₂) (h₂: c₂ ≈ c₃): c₁ ≈ c₃
      | _, _ => Iff.trans (h₁ _ _) (h₂ _ _)
  end Blended

  /-
  ### Behavioral Equivalence is a Congruence
  -/

  private def congr_prog₁ := [Imp|
    X := 0;
    ite (X = 0) {
      Y := 0
    } else {
      Y := 42
    }
  ]

  private def congr_prog₂ := [Imp|
    X := 0;
    ite (X = 0) {
      Y := X - X
    } else {
      Y := 42
    }
  ]

  namespace Term
    theorem Command.skip.congr: [Imp| skip] ≈ [Imp| skip]
      | _, _ => Iff.refl _

    theorem Command.assign.congr {id: String} {e₁ e₂: Arith} (h₁: e₁ ≈ e₂): [Imp| ‹id› := ‹e₁› ].equiv [Imp| ‹id› := ‹e₂›]
      | s₁, s₂ =>
        have h {id: String} {e₁ e₂: Arith} (h: e₁ ≈ e₂): (s₁ =[[Imp| ‹id› := ‹e₁›]]=> s₂) → s₁ =[[Imp| ‹id› := ‹e₂›]]=> s₂
          | .assign _ h₁ =>
            have h₂: e₂.eval _ = _ :=
              calc e₂.eval _
                _ = e₁.eval _ := Arith.equiv.symm h _
                _ = _         := h₁
            .assign _ h₂
        have h₂ := Arith.equiv.symm h₁
        ⟨h h₁, h h₂⟩

    theorem Command.seq.congr {c₁ c₂ c₃ c₄: Command} (h₁: c₁ ≈ c₂) (h₂: c₃ ≈ c₄): [Imp| ‹c₁›; ‹c₃›] ≈ [Imp| ‹c₂›; ‹c₄›]
      | s₁, s₂ =>
        have h {c₁ c₂ c₃ c₄: Command} (h₁: c₁ ≈ c₂) (h₂: c₃ ≈ c₄): (s₁ =[[Imp| ‹c₁›; ‹c₃›]]=> s₂) → s₁ =[[Imp| ‹c₂›; ‹c₄›]]=> s₂
          | .seq _ _ _ h₃ h₄ =>
            have h₅: _ =[c₂]=> _ :=
              have ⟨h, _⟩ := h₁ _ _
              h h₃
            have h₆: _ =[c₄]=> _ :=
              have ⟨h, _⟩ := h₂ _ _
              h h₄
            .seq _ _ _ h₅ h₆
        have h₃ := Command.equiv.symm h₁
        have h₄ := Command.equiv.symm h₂
        ⟨h h₁ h₂, h h₃ h₄⟩

    theorem Command.if.congr {c₁ c₂: Logic} {t₁ t₂ f₁ f₂: Command} (h₁: c₁ ≈ c₂) (h₂: t₁ ≈ t₂) (h₃: f₁ ≈ f₂): [Imp| ite (‹c₁›) { ‹t₁› } else { ‹f₁› }] ≈ [Imp| ite (‹c₂›) { ‹t₂› } else { ‹f₂› }]
      | s₁, s₂ =>
        have h {c₁ c₂: Logic} {t₁ t₂ f₁ f₂: Command} (h₁: c₁ ≈ c₂) (h₂: t₁ ≈ t₂) (h₃: f₁ ≈ f₂): (s₁ =[[Imp| ite (‹c₁›) { ‹t₁› } else { ‹f₁› }]]=> s₂) → s₁ =[[Imp| ite (‹c₂›) { ‹t₂› } else { ‹f₂› }]]=> s₂
          | .ifTrue _ _ h₄ h₅ =>
            have h₆: c₂.eval _ = true :=
              calc c₂.eval _
                _ = c₁.eval _ := Logic.equiv.symm h₁ _
                _ = true      := h₄
            have h₇ :=
              have ⟨h, _⟩ := h₂ _ _
              h h₅
            .ifTrue _ _ h₆ h₇
          | .ifFalse _ _ h₄ h₅ =>
            have h₆: c₂.eval _ = false :=
              calc c₂.eval _
                _ = c₁.eval _ := Logic.equiv.symm h₁ _
                _ = false     := h₄
            have h₇ :=
              have ⟨h, _⟩ := h₃ _ _
              h h₅
            .ifFalse _ _ h₆ h₇
        have h₄ := Logic.equiv.symm h₁
        have h₅ := Command.equiv.symm h₂
        have h₆ := Command.equiv.symm h₃
        ⟨h h₁ h₂ h₃, h h₄ h₅ h₆⟩

    theorem Command.while.congr {c₁ c₂: Logic} {b₁ b₂: Command} (h₁: c₁ ≈ c₂) (h₂: b₁ ≈ b₂): [Imp| while (‹c₁›) { ‹b₁› }] ≈ [Imp| while (‹c₂›) { ‹b₂› }]
      | s₁, s₂ =>
        have h {c₁ c₂: Logic} {b₁ b₂: Command} (h₁: c₁ ≈ c₂) (h₂: b₁ ≈ b₂): (s₁ =[[Imp| while (‹c₁›) { ‹b₁› }]]=> s₂) → s₁ =[[Imp| while (‹c₂›) { ‹b₂› }]]=> s₂
          | .whileTrue _ _ _ h₄ h₅ h₆ =>
            have h₇: c₂.eval _ = true :=
              calc c₂.eval _
                 _ = c₁.eval _ := Logic.equiv.symm h₁ _
                 _ = true      := h₄
            have h₈: _ =[b₂]=> _ :=
              have ⟨h, _⟩ := h₂ _ _
              h h₅
            have h₉: _ =[[Imp| while (‹c₂›) { ‹b₂› }]]=> _ :=
              -- have h₁ := h₁ _
              -- have ⟨h₁, _⟩ := h₂ _ _
              -- h₆ h₁ h₂
              sorry
            .whileTrue _ _ _ h₇ h₈ h₉
          | .whileFalse _ h₄ =>
            have h₅: c₂.eval _ = false :=
              calc c₂.eval _
                _ = c₁.eval _ := Logic.equiv.symm h₁ _
                _ = false     := h₄
            .whileFalse _ h₅
        have h₃ := Logic.equiv.symm h₁
        have h₄ := Command.equiv.symm h₂
        ⟨h h₁ h₂, h h₃ h₄⟩

    example: congr_prog₁ ≈ congr_prog₂
      | _, _ =>
        have mp
          | .seq _ _ _ _ (.ifTrue _ _ _ (.assign _ _)) => sorry
          | .seq _ _ _ _ (.ifFalse _ _ _ (.assign _ _)) => sorry
        have mpr
          | .seq _ _ _ _ (.ifTrue _ _ _ (.assign _ _)) => sorry
          | .seq _ _ _ _ (.ifFalse _ _ _ (.assign _ _)) => sorry
        ⟨mp, mpr⟩
  end Term

  namespace Tactic
    theorem Command.skip.congr: [Imp| skip] ≈ [Imp| skip] := by
      intro s₁ s₂
      apply Iff.refl

    theorem Command.assign.congr {id: String} {e₁ e₂: Arith} (h₁: e₁ ≈ e₂): [Imp| ‹id› := ‹e₁› ].equiv [Imp| ‹id› := ‹e₂›] := by
      intro s₁ s₂
      have h {id: String} {e₁ e₂: Arith} (h₁: e₁ ≈ e₂): (s₁ =[[Imp| ‹id› := ‹e₁›]]=> s₂) → s₁ =[[Imp| ‹id› := ‹e₂›]]=> s₂ := by
        intro
        | .assign _ h =>
          rw [h₁] at h
          exact CommandEval.assign _ h
      apply Iff.intro
      · exact h h₁
      · apply h
        · exact Arith.equiv.symm h₁

    theorem Command.seq.congr {c₁ c₂ c₃ c₄: Command} (h₁: c₁ ≈ c₂) (h₂: c₃ ≈ c₄): [Imp| ‹c₁›; ‹c₃›] ≈ [Imp| ‹c₂›; ‹c₄›] := by
      intro s₁ s₂
      have h {c₁ c₂ c₃ c₄: Command} (h₁: c₁ ≈ c₂) (h₂: c₃ ≈ c₄): (s₁ =[[Imp| ‹c₁›; ‹c₃›]]=> s₂) → s₁ =[[Imp| ‹c₂›; ‹c₄›]]=> s₂ := by
        intro
        | .seq _ _ _ h₃ h₄ =>
          rw [h₁] at h₃
          rw [h₂] at h₄
          exact CommandEval.seq _ _ _ h₃ h₄
      apply Iff.intro
      · apply h h₁ h₂
      · apply h
        · exact Command.equiv.symm h₁
        · exact Command.equiv.symm h₂

    theorem Command.if.congr {c₁ c₂: Logic} {t₁ t₂ f₁ f₂: Command} (h₁: c₁ ≈ c₂) (h₂: t₁ ≈ t₂) (h₃: f₁ ≈ f₂): [Imp| ite (‹c₁›) { ‹t₁› } else { ‹f₁› }] ≈ [Imp| ite (‹c₂›) { ‹t₂› } else { ‹f₂› }] := by
      intro s₁ s₂
      have h {c₁ c₂: Logic} {t₁ t₂ f₁ f₂: Command} (h₁: c₁ ≈ c₂) (h₂: t₁ ≈ t₂) (h₃: f₁ ≈ f₂): (s₁ =[[Imp| ite (‹c₁›) { ‹t₁› } else { ‹f₁› }]]=> s₂) → s₁ =[[Imp| ite (‹c₂›) { ‹t₂› } else { ‹f₂› }]]=> s₂ := by
        intro
        | .ifTrue _ _ h₄ h₅ =>
          rw [h₁] at h₄
          rw [h₂] at h₅
          exact CommandEval.ifTrue _ _ h₄ h₅
        | .ifFalse _ _ h₄ h₅ =>
          rw [h₁] at h₄
          rw [h₃] at h₅
          exact CommandEval.ifFalse _ _ h₄ h₅
      apply Iff.intro
      · apply h h₁ h₂ h₃
      · apply h
        · exact Logic.equiv.symm h₁
        · exact Command.equiv.symm h₂
        · exact Command.equiv.symm h₃

    theorem Command.while.congr {c₁ c₂: Logic} {b₁ b₂: Command} (h₁: c₁ ≈ c₂) (h₂: b₁ ≈ b₂): [Imp| while (‹c₁›) { ‹b₁› }] ≈ [Imp| while (‹c₂›) { ‹b₂› }] := by
      intro s₁ s₂
      have h {c₁ c₂: Logic} {b₁ b₂: Command} (h₁: c₁ ≈ c₂) (h₂: b₁ ≈ b₂): (s₁ =[[Imp| while (‹c₁›) { ‹b₁› }]]=> s₂) → s₁ =[[Imp| while (‹c₂›) { ‹b₂› }]]=> s₂ := by
        intro
        | .whileTrue s₃ s₄ s₅ h₃ h₄ h₅ =>
          rw [h₁] at h₃
          rw [h₂] at h₄
          have ih: s₄ =[[Imp| while (‹c₂›) { ‹b₂›}]]=> s₅ := by
            sorry
          exact CommandEval.whileTrue _ _ _ h₃ h₄ ih
        | .whileFalse _ h₃ =>
          rw [h₁] at h₃
          exact CommandEval.whileFalse _ h₃
      apply Iff.intro
      · exact h h₁ h₂
      · apply h
        · exact Logic.equiv.symm h₁
        · exact Command.equiv.symm h₂

    example: congr_prog₁.equiv congr_prog₂ := by sorry
  end Tactic

  namespace Blended
    theorem Command.skip.congr: [Imp| skip] ≈ [Imp| skip]
      | _, _ => Iff.refl _

    theorem Command.assign.congr {id: String} {e₁ e₂: Arith} (h₁: e₁ ≈ e₂): [Imp| ‹id› := ‹e₁› ].equiv [Imp| ‹id› := ‹e₂›]
      | s₁, s₂ =>
        have h {id: String} {e₁ e₂: Arith} (h₁: e₁ ≈ e₂): (s₁ =[[Imp| ‹id› := ‹e₁›]]=> s₂) → s₁ =[[Imp| ‹id› := ‹e₂›]]=> s₂
          | .assign _ h => by
            rw [h₁] at h
            exact CommandEval.assign _ h
        have h₂ := Arith.equiv.symm h₁
        ⟨h h₁, h h₂⟩

    theorem Command.seq.congr {c₁ c₂ c₃ c₄: Command} (h₁: c₁ ≈ c₂) (h₂: c₃ ≈ c₄): [Imp| ‹c₁›; ‹c₃›] ≈ [Imp| ‹c₂›; ‹c₄›]
      | s₁, s₂ =>
        have h {c₁ c₂ c₃ c₄: Command} (h₁: c₁ ≈ c₂) (h₂: c₃ ≈ c₄): (s₁ =[[Imp| ‹c₁›; ‹c₃›]]=> s₂) → s₁ =[[Imp| ‹c₂›; ‹c₄›]]=> s₂
          | .seq _ _ _ h₃ h₄ => by
            rw [h₁] at h₃
            rw [h₂] at h₄
            exact CommandEval.seq _ _ _ h₃ h₄
        have h₃ := Command.equiv.symm h₁
        have h₄ := Command.equiv.symm h₂
        ⟨h h₁ h₂, h h₃ h₄⟩

    theorem Command.if.congr {c₁ c₂: Logic} {t₁ t₂ f₁ f₂: Command} (h₁: c₁ ≈ c₂) (h₂: t₁ ≈ t₂) (h₃: f₁ ≈ f₂): [Imp| ite (‹c₁›) { ‹t₁› } else { ‹f₁› }] ≈ [Imp| ite (‹c₂›) { ‹t₂› } else { ‹f₂› }]
      | s₁, s₂ =>
        have h {c₁ c₂: Logic} {t₁ t₂ f₁ f₂: Command} (h₁: c₁ ≈ c₂) (h₂: t₁ ≈ t₂) (h₃: f₁ ≈ f₂): (s₁ =[[Imp| ite (‹c₁›) { ‹t₁› } else { ‹f₁› }]]=> s₂) → s₁ =[[Imp| ite (‹c₂›) { ‹t₂› } else { ‹f₂› }]]=> s₂
          | .ifTrue _ _ h₄ h₅ => by
            rw [h₁] at h₄
            rw [h₂] at h₅
            exact CommandEval.ifTrue _ _ h₄ h₅
          | .ifFalse _ _ h₄ h₅ => by
            rw [h₁] at h₄
            rw [h₃] at h₅
            exact CommandEval.ifFalse _ _ h₄ h₅
        have h₄ := Logic.equiv.symm h₁
        have h₅ := Command.equiv.symm h₂
        have h₆ := Command.equiv.symm h₃
        ⟨h h₁ h₂ h₃, h h₄ h₅ h₆⟩

    theorem Command.while.congr {c₁ c₂: Logic} {b₁ b₂: Command} (h₁: c₁ ≈ c₂) (h₂: b₁ ≈ b₂): [Imp| while (‹c₁›) { ‹b₁› }] ≈ [Imp| while (‹c₂›) { ‹b₂› }]
      | s₁, s₂ =>
        have h {c₁ c₂: Logic} {b₁ b₂: Command} (h₁: c₁ ≈ c₂) (h₂: b₁ ≈ b₂): (s₁ =[[Imp| while (‹c₁›) { ‹b₁› }]]=> s₂) → s₁ =[[Imp| while (‹c₂›) { ‹b₂› }]]=> s₂
          | .whileTrue s₃ s₄ s₅ h₃ h₄ h₅ => by
            rw [h₁] at h₃
            rw [h₂] at h₄
            have h₅: CommandEval (.while c₂ b₂) s₄ s₅ :=
              -- have h₁ := h₁ _
              -- have ⟨h₁, _⟩ := h₂ _ _
              -- h₆ h₁ h₂
              sorry
            exact CommandEval.whileTrue _ _ _ h₃ h₄ h₅
          | .whileFalse _ h₃ => by
            rw [h₁] at h₃
            exact CommandEval.whileFalse _ h₃
        have h₃ := Logic.equiv.symm h₁
        have h₄ := Command.equiv.symm h₂
        ⟨h h₁ h₂, h h₃ h₄⟩

    example: congr_prog₁.equiv congr_prog₂ := sorry
  end Blended

  /-
  ## Program Transformations
  -/

  def Arith.transform_sound (t: Arith → Arith): Prop := ∀ e: Arith, e ≈ (t e)
  def Logic.transform_sound (t: Logic → Logic): Prop := ∀ b: Logic, b ≈ (t b)
  def Command.transform_sound (t: Command → Command): Prop := ∀ c: Command, c ≈ (t c)

  /-
  ### Constant Folding Optimization
  -/

  @[reducible]
  def _root_.SoftwareFoundations.LogicalFoundations.Imp.Arith.constFold: Arith → Arith
    | .num n => .num n
    | .ident id => .ident id
    | .plus e₁ e₂ =>
      match constFold e₁, constFold e₂ with
        | .num n₁, .num n₂ => .num (n₁ + n₂)
        | e₁, e₂ => .plus e₁ e₂
    | .minus e₁ e₂ =>
      match constFold e₁, constFold e₂ with
        | .num n₁, .num n₂ => .num (n₁ - n₂)
        | e₁, e₂ => .minus e₁ e₂
    | .mult e₁ e₂ =>
      match constFold e₁, constFold e₂ with
        | .num n₁, .num n₂ => .num (n₁ * n₂)
        | e₁, e₂ => .mult e₁ e₂

  example: [Arith| (1 + 2) * X].constFold = [Arith| 3 * X] := rfl
  example: [Arith| X - ((0 * 6) + Y)].constFold = [Arith| X - (0 + Y)] := rfl

  @[reducible]
  def _root_.SoftwareFoundations.LogicalFoundations.Imp.Logic.constFold: Logic → Logic
    | .true => .true
    | .false => .false
    | .eq e₁ e₂ =>
      match e₁.constFold, e₂.constFold with
        | .num n₁, .num n₂ => if n₁ == n₂ then .true else .false
        | e₁, e₂ => .eq e₁ e₂
    | .neq e₁ e₂ =>
      match e₁.constFold, e₂.constFold with
        | .num n₁, .num n₂ => if n₁ != n₂ then .true else .false
        | e₁, e₂ => .eq e₁ e₂
    | .le e₁ e₂ =>
      match e₁.constFold, e₂.constFold with
        | .num n₁, .num n₂ => if n₁ ≤ n₂ then .true else .false
        | e₁, e₂ => .eq e₁ e₂
    | .gt e₁ e₂ =>
      match e₁.constFold, e₂.constFold with
        | .num n₁, .num n₂ => if n₁ > n₂ then .true else .false
        | e₁, e₂ => .eq e₁ e₂
    | .not b =>
      match constFold b with
        | .true => .false
        | .false => .true
        | b => .not b
    | .and b₁ b₂ =>
      match constFold b₁, constFold b₂ with
        -- Note: Avoiding the short-circuiting `_, .false` and `.false, _` cases
        -- as that can change the termination properties of the `Imp` program.
        | .true, .true => .true
        | .true, .false => .false
        | .false, .true => .false
        | .false, .false => .false
        | b₁, b₂ => .and b₁ b₂

  example: [Logic| tru && !(fls && tru)].constFold = [Logic| tru] := rfl
  example: [Logic| (X = Y) && (0 = (2 - (1 + 1)))].constFold = [Logic| (X = Y) && tru] := rfl

  @[reducible]
  def _root_.SoftwareFoundations.LogicalFoundations.Imp.Command.constFold: Command → Command
    | .skip => .skip
    | .assign id e => .assign id e.constFold
    | .seq c₁ c₂ => .seq c₁.constFold c₂.constFold
    | .if c t f =>
      let t: Command := t.constFold
      let f: Command := f.constFold
      match c.constFold with
        | .true => t
        | .false => f
        | c => .if c t f
    | .while c b =>
      match c.constFold with
        | .true => .while .true .skip
        | .false => .skip
        | c => .while c b.constFold

  example:
    [Imp|
      X := 4 + 5;
      Y := X - 3;
      ite ((X - Y) = (2 + 4)) {
        skip
      } else {
        Y := 0
      };
      ite (0 ≤ (4 - (2 + 1))) {
        Y := 0
      } else {
        skip
      };
      while (Y = 0) {
        X := X + 1
      }
    ].constFold
    =
    [Imp|
      X := 9;
      Y := X - 3;
      ite ((X - Y) = 6) {
        skip
      } else {
        Y := 0
      };
      Y := 0;
      while (Y = 0) {
        X := X + 1
      }
    ]
    := rfl

  /-
  ### Soundness of Constant Folding
  -/

  namespace Term
    theorem Arith.constFold.sound: Arith.transform_sound Arith.constFold
      | .num _, _ | .ident _, _ => rfl
      | .plus e₁ e₂, s =>
        -- have h (e₁ e₂: Arith): (Arith.plus e₁ e₂).eval s = (Arith.plus e₁.constFold e₂.constFold).eval s :=
        --   have ih₁ := sound e₁ s
        --   have ih₂ := sound e₂ s
        --   calc (Arith.plus e₁ e₂).eval s
        --     _ = e₁.eval s + e₂.eval s                         := rfl
        --     _ = e₁.constFold.eval s + e₂.constFold.eval s     := congr (congrArg Nat.add ih₁) ih₂
        --     _ = (Arith.plus e₁.constFold e₂.constFold).eval s := rfl
        match e₁.constFold with
          | .num n₁ =>
            match e₂.constFold with
              | .num n₂ =>
                -- calc (Arith.plus (Arith.num n₁) (Arith.num n₂)).eval s
                --   _ = (Arith.plus (Arith.num n₁).constFold (Arith.num n₂).constFold).eval s := h (Arith.num n₁) (Arith.num n₂)
                --   _ = (Arith.plus (Arith.num n₁) (Arith.num n₂)).constFold.eval s := rfl
                sorry
              | _ => sorry
          | _ => sorry
      | .minus e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        have h :=
          calc [Arith| ‹e₁› - ‹e₂›].eval s
            _ = e₁.eval s - e₂.eval s                                         := rfl
            _ = e₁.constFold.eval s - e₂.constFold.eval s                     := congr (congrArg Nat.sub ih₁) ih₂
            _ = [Arith| ‹e₁.constFold› - ‹e₂.constFold›].eval s := rfl
            -- _ = [Arith| ‹e₁› - ‹e₂›].eval s                     := sorry
        sorry
      | .mult e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        have h :=
          calc [Arith| ‹e₁› * ‹e₂›].eval s
            _ = e₁.eval s * e₂.eval s                                         := rfl
            _ = e₁.constFold.eval s * e₂.constFold.eval s                     := congr (congrArg Nat.mul ih₁) ih₂
            _ = [Arith| ‹e₁.constFold› * ‹e₂.constFold›].eval s := rfl
            -- _ = [Arith| ‹e₁› * ‹e₂›].eval s                     := sorry
        sorry

    theorem Logic.constFold.sound: Logic.transform_sound Logic.constFold := sorry

    theorem Command.constFold.sound: Command.transform_sound Command.constFold
      | .skip, _, _ => ⟨id, id⟩
      | .assign id e, s₁, s₂ =>
        have h := Arith.constFold.sound e
        Command.assign.congr h s₁ s₂
      | .seq c₁ c₂, s₁, s₂ =>
        have h₁ := sound c₁
        have h₂ := sound c₂
        Command.seq.congr h₁ h₂ s₁ s₂
      | .if c t f, s₁, s₂ =>
        have h₁ := Logic.constFold.sound c
        have h₂ := sound t
        have h₃ := sound f
        -- Command.if.congr h₁ h₂ h₃ s₁ s₂
        sorry
      | .while c b, s₁, s₂ =>
        have h₁ := Logic.constFold.sound c
        have h₂ := sound b
        -- Command.while.congr h₁ h₂ s₁ s₂
        sorry
  end Term

  namespace Tactic
    theorem Arith.constFold.sound: Arith.transform_sound Arith.constFold := by sorry
    theorem Logic.constFold.sound: Logic.transform_sound Logic.constFold := by sorry
    theorem Command.constFold.sound: Command.transform_sound Command.constFold := by sorry
  end Tactic

  namespace Blended
    theorem Arith.constFold.sound: Arith.transform_sound Arith.constFold := sorry
    theorem Logic.constFold.sound: Logic.transform_sound Logic.constFold := sorry
    theorem Command.constFold.sound: Command.transform_sound Command.constFold := sorry
  end Blended

  /-
  ### Soundness of `0 + n` Elimination, Redux
  -/

  @[reducible]
  def _root_.SoftwareFoundations.LogicalFoundations.Imp.Arith.opt0Plus: Arith → Arith
    | .plus (.num 0) e₂ => e₂.opt0Plus
    | .plus e₁ e₂ => .plus e₁.opt0Plus e₂.opt0Plus
    | .minus e₁ e₂ => .minus e₁.opt0Plus e₂.opt0Plus
    | .mult e₁ e₂ => .mult e₁.opt0Plus e₂.opt0Plus
    | e => e

  @[reducible]
  def _root_.SoftwareFoundations.LogicalFoundations.Imp.Logic.opt0Plus: Logic → Logic
    | .eq e₁ e₂ => .eq e₁.opt0Plus e₂.opt0Plus
    | .neq e₁ e₂ => .neq e₁.opt0Plus e₂.opt0Plus
    | .le e₁ e₂ => .le e₁.opt0Plus e₂.opt0Plus
    | .gt e₁ e₂ => .gt e₁.opt0Plus e₂.opt0Plus
    | .not b => .not (opt0Plus b)
    | .and b₁ b₂ => .and (opt0Plus b₁) (opt0Plus b₂)
    | b => b

  @[reducible]
  def _root_.SoftwareFoundations.LogicalFoundations.Imp.Command.opt0Plus: Command → Command
    | .assign id e => .assign id e.opt0Plus
    | .seq c₁ c₂ => .seq (opt0Plus c₁) (opt0Plus c₂)
    | .if c t f => .if c.opt0Plus (opt0Plus t) (opt0Plus f)
    | .while c b => .while c.opt0Plus (opt0Plus b)
    | c => c

  example: [Imp| while (X ≠ 0) { X := 0 + X - 1 }].opt0Plus = [Imp| while (X ≠ 0) { X := X - 1 }] := rfl

  namespace Term
    theorem Arith.opt0Plus.sound: Arith.transform_sound Arith.opt0Plus
      | .num _, s | .ident _, s => rfl
      | .plus e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        match e₁ with
          | .num n =>
            match n with
              | .zero =>
                calc [Arith| 0 + ‹e₂›].eval s
                  _ = [Arith| 0].eval s + e₂.eval s                                       := rfl
                  _ = [Arith| 0].opt0Plus.eval s + e₂.opt0Plus.eval s                     := congr (congrArg Nat.add ih₁) ih₂
                  _ = [Arith| ‹[Arith| 0].opt0Plus› + ‹e₂.opt0Plus›].eval s := rfl
                  _ = [Arith| 0 + ‹e₂›].opt0Plus.eval s                            := by simp -- congrArg (Arith.eval s) rfl -- TODO: Remove Tactic Block
                  _ = e₂.opt0Plus.eval s                                                  := rfl
              | .succ _ =>
                calc [Arith| ‹num:Nat.succ _› + ‹e₂›].eval s
                  _ = (Arith.num (.succ _)).eval s + e₂.eval s                   := rfl
                  _ = (Arith.num (.succ _)).opt0Plus.eval s + e₂.opt0Plus.eval s := congr (congrArg Nat.add ih₁) ih₂
                  _ = (Arith.plus (.num (.succ _)) e₂).opt0Plus.eval s           := rfl
          | .ident _ =>
            calc [Arith| ‹id:_› + ‹e₂›].eval s
              _ = [Arith| ‹id:_›].eval s + e₂.eval s                   := rfl
              _ = [Arith| ‹id:_›].opt0Plus.eval s + e₂.opt0Plus.eval s := congr (congrArg Nat.add ih₁) ih₂
              _ = [Arith| ‹id:_› + ‹e₂›].opt0Plus.eval s        := rfl
          | .plus _ _ =>
            calc [Arith| (‹_› + ‹_›) + ‹e₂›].eval s
              _ = [Arith| ‹_› + ‹_›].eval s + e₂.eval s                   := rfl
              _ = [Arith| ‹_› + ‹_›].opt0Plus.eval s + e₂.opt0Plus.eval s := congr (congrArg Nat.add ih₁) ih₂
              _ = [Arith| (‹_› + ‹_›) + ‹e₂›].opt0Plus.eval s      := rfl
          | .minus _ _ =>
            calc [Arith| (‹_› - ‹_›) + ‹e₂›].eval s
              _ = [Arith| ‹_› - ‹_›].eval s + e₂.eval s                   := rfl
              _ = [Arith| ‹_› - ‹_›].opt0Plus.eval s + e₂.opt0Plus.eval s := congr (congrArg Nat.add ih₁) ih₂
              _ = [Arith| (‹_› - ‹_›) + ‹e₂›].opt0Plus.eval s      := rfl
          | .mult _ _ =>
            calc [Arith| (‹_› * ‹_›) + ‹e₂›].eval s
              _ = [Arith| ‹_› * ‹_›].eval s + e₂.eval s                   := rfl
              _ = [Arith| ‹_› * ‹_›].opt0Plus.eval s + e₂.opt0Plus.eval s := congr (congrArg Nat.add ih₁) ih₂
              _ = [Arith| (‹_› * ‹_›) + ‹e₂›].opt0Plus.eval s      := rfl
      | .minus e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        calc [Arith| ‹e₁› - ‹e₂›].eval s
          _ = e₁.eval s - e₂.eval s                              := rfl
          _ = e₁.opt0Plus.eval s - e₂.opt0Plus.eval s            := congr (congrArg Nat.sub ih₁) ih₂
          _ = [Arith| ‹e₁› - ‹e₂›].opt0Plus.eval s := rfl
      | .mult e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        calc [Arith| ‹e₁› * ‹e₂›].eval s
          _ = e₁.eval s * e₂.eval s                              := rfl
          _ = e₁.opt0Plus.eval s * e₂.opt0Plus.eval s            := congr (congrArg Nat.mul ih₁) ih₂
          _ = [Arith| ‹e₁› * ‹e₂›].opt0Plus.eval s := rfl

    theorem Logic.opt0Plus.sound: Logic.transform_sound Logic.opt0Plus
      | .true, _ | .false, _ => rfl
      | .eq e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        calc [Logic| ‹e₁› = ‹e₂›].eval s
          _ = BEq.beq (e₁.eval s) (e₂.eval s)                   := rfl
          _ = BEq.beq (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s) := congr (congrArg BEq.beq ih₁) ih₂
          _ = [Logic| ‹e₁› = ‹e₂›].opt0Plus.eval s                  := rfl
      | .neq e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        calc [Logic| ‹e₁› ≠ ‹e₂›].eval s
          _ = not (BEq.beq (e₁.eval s) (e₂.eval s))                   := rfl
          _ = not (BEq.beq (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s)) := sorry-- congr (congr (congrArg (not ∘ BEq.beq)) ih₁) ih₂
          _ = [Logic| ‹e₁› ≠ ‹e₂›].opt0Plus.eval s                       := rfl
      | .le e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        sorry
        -- calc [Logic| ‹e₁› ≤ ‹e₂›].eval s
        --   _ = (LE.le (e₁.eval s) (e₂.eval s): Bool)                   := rfl
        --   _ = (LE.le (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s): Bool) := congr (congrArg LE.le ih₁) ih₂
        --   _ = [Logic| ‹e₁› ≤ ‹e₂›].opt0Plus.eval s                        := rfl
      | .gt e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        sorry
        -- calc [Logic| ‹e₁› > ‹e₂›].eval s
        --   _ = (GT.gt (e₁.eval s) (e₂.eval s): Bool)                   := rfl
        --   _ = (GT.gt (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s): Bool) := congr (congrArg GT.gt ih₁) ih₂
        --   _ = [Logic| ‹e₁› > ‹e₂›].opt0Plus.eval s                        := rfl
      | .not b, s =>
        have ih := sound b s
        calc [Logic| ! ‹b›].eval s
          _ = not (b.eval s)                := rfl
          _ = not (b.opt0Plus.eval s)       := congrArg not ih
          _ = [Logic| ! ‹b› ].opt0Plus.eval s := rfl
      | .and b₁ b₂, s =>
        have ih₁ := sound b₁ s
        have ih₂ := sound b₂ s
        calc [Logic| ‹b₁› && ‹b₂› ].eval s
          _ = and (b₁.eval s) (b₂.eval s)                   := rfl
          _ = and (b₁.opt0Plus.eval s) (b₂.opt0Plus.eval s) := congr (congrArg and ih₁) ih₂
          _ = [Logic| ‹b₁› && ‹b₂› ].opt0Plus.eval s             := rfl

    theorem Command.opt0Plus.sound: Command.transform_sound Command.opt0Plus
      | .skip, _, _ => ⟨id, id⟩
      | .assign _ e, s₁, s₂ =>
        have h := Arith.opt0Plus.sound e
        Command.assign.congr h s₁ s₂
      | .seq c₁ c₂, s₁, s₂ =>
        have h₁ := sound c₁
        have h₂ := sound c₂
        Command.seq.congr h₁ h₂ s₁ s₂
      | .if c t f, s₁, s₂ =>
        have h₁ := Logic.opt0Plus.sound c
        have h₂ := sound t
        have h₃ := sound f
        Command.if.congr h₁ h₂ h₃ s₁ s₂
      | .while c b, s₁, s₂ =>
        have h₁ := Logic.opt0Plus.sound c
        have h₂ := sound b
        Command.while.congr h₁ h₂ s₁ s₂
  end Term

  namespace Tactic
    theorem Arith.opt0Plus.sound: Arith.transform_sound Arith.opt0Plus := by
      -- intro e s
      -- induction e
      -- <;> try rfl
      -- case minus | mult =>
      --   unfold Arith.opt0Plus Arith.eval
      --   simp_all
      -- case plus e₁ e₂ ih₁ ih₂ =>
      --   cases e₁
      --   case num n =>
      --     cases n with
      --       | zero =>
      --         repeat rw [← ih₂]
      --         simp_all
      --       | succ n =>
      --         unfold Arith.opt0Plus
      --         simp_all
      --   case ident | plus | minus | mult =>
      --     unfold Arith.opt0Plus Arith.eval
      --     simp_all
       sorry

    theorem Logic.opt0Plus.sound: Logic.transform_sound Logic.opt0Plus := by
      intro b s
      induction b
      <;> try rfl
      case eq | neq | le | gt =>
        unfold Logic.opt0Plus Logic.eval
        repeat rw [← Arith.opt0Plus.sound]
      case not | and =>
        unfold Logic.opt0Plus Logic.eval
        simp_all

    theorem Command.opt0Plus.sound: Command.transform_sound Command.opt0Plus := by sorry
  end Tactic

  namespace Blended
    theorem Arith.opt0Plus.sound: Arith.transform_sound Arith.opt0Plus
      | .num _, _ | .ident _, _ => rfl
      | .plus e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        match e₁ with
          | .num n =>
            match n with
              | .zero => by simp_all
              | .succ _ =>
                calc [Arith| ‹num:Nat.succ _› + ‹e₂›].eval s
                  _ = (Arith.num (.succ _)).eval s + e₂.eval s                   := by rfl
                  _ = (Arith.num (.succ _)).opt0Plus.eval s + e₂.opt0Plus.eval s := by rw [ih₁, ih₂]
                  _ = (Arith.plus (.num (.succ _)) e₂).opt0Plus.eval s           := by rfl
          | .ident _ | .plus _ _ | .minus _ _ | .mult _ _ =>
            by
              unfold Arith.eval
              rw [ih₁, ih₂]
      | .minus e₁ e₂, s | .mult e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        by
          unfold Arith.eval
          rw [ih₁, ih₂]

    theorem Logic.opt0Plus.sound: Logic.transform_sound Logic.opt0Plus
      | .true, _ | .false, _ => rfl
      | .eq e₁ e₂, s | .neq e₁ e₂, s | .le e₁ e₂, s | .gt e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        by
          unfold Logic.eval
          rw [ih₁, ih₂]
      | .not b, s =>
        have ih := sound b s
        by
          unfold Logic.eval
          rw [ih]
      | .and b₁ b₂, s =>
        have ih₁ := sound b₁ s
        have ih₂ := sound b₂ s
        by
          unfold Logic.eval
          rw [ih₁, ih₂]

    theorem Command.opt0Plus.sound: Command.transform_sound Command.opt0Plus
      | .skip, _, _ => ⟨id, id⟩
      | .assign _ e, s₁, s₂ =>
        have h := Arith.opt0Plus.sound e
        Command.assign.congr h s₁ s₂
      | .seq c₁ c₂, s₁, s₂ =>
        have h₁ := sound c₁
        have h₂ := sound c₂
        Command.seq.congr h₁ h₂ s₁ s₂
      | .if c t f, s₁, s₂ =>
        have h₁ := Logic.opt0Plus.sound c
        have h₂ := sound t
        have h₃ := sound f
        Command.if.congr h₁ h₂ h₃ s₁ s₂
      | .while c b, s₁, s₂ =>
        have h₁ := Logic.opt0Plus.sound c
        have h₂ := sound b
        Command.while.congr h₁ h₂ s₁ s₂
  end Blended

  /-
  #### Transitive Optimization
  -/

  @[reducible]
  def Command.opt (c: Command): Command := c.constFold.opt0Plus

  namespace Term
    theorem Command.opt.sound: Command.transform_sound Command.opt := sorry
  end Term

  namespace Tactic
    theorem Command.opt.sound: Command.transform_sound Command.opt := by sorry
  end Tactic

  namespace Blended
    theorem Command.opt.sound: Command.transform_sound Command.opt := sorry
  end Blended

  /-
  ## Proving Inequivalence
  -/

  @[reducible]
  def _root_.SoftwareFoundations.LogicalFoundations.Imp.Arith.subst (within: Arith) (var: String) (repl: Arith): Arith :=
    match within with
      | .num n => .num n
      | .ident id => if id == var then repl else .ident id
      | .plus e₁ e₂ => .plus (subst e₁ var repl) (subst e₂ var repl)
      | .minus e₁ e₂ => .minus (subst e₁ var repl) (subst e₂ var repl)
      | .mult e₁ e₂ => .mult (subst e₁ var repl) (subst e₂ var repl)

  example: [Arith| Y + X].subst "X" [Arith| 42 + 53] = [Arith| Y + (42 + 53)] := rfl

  def Arith.subst.equiv: Prop := ∀ id₁ id₂ e₁ e₂, [Imp| ‹id₁› := ‹e₁›; ‹id₂› := ‹e₂›] ≈ [Imp| ‹id₁› := ‹e₁›; ‹id₂› := ‹e₂.subst id₁ e₁›]

  namespace Term
    theorem Arith.subst.equiv.inequiv: ¬Arith.subst.equiv := sorry
  end Term

  namespace Tactic
    theorem Arith.subst.equiv.inequiv: ¬Arith.subst.equiv := by sorry
  end Tactic

  namespace Blended
    theorem Arith.subst.equiv.inequiv: ¬Arith.subst.equiv := sorry
  end Blended

  inductive OccursCheck (var: String): Arith → Prop
    | num {n: Nat}: OccursCheck var (.num n)
    | ident {id: String} (h: id ≠ var): OccursCheck var (.ident id)
    | plus {e₁ e₂: Arith} (h₁: OccursCheck var e₁) (h₂: OccursCheck var e₁): OccursCheck var (.plus e₁ e₂)
    | minus {e₁ e₂: Arith} (h₁: OccursCheck var e₁) (h₂: OccursCheck var e₁): OccursCheck var (.minus e₁ e₂)
    | mult {e₁ e₂: Arith} (h₁: OccursCheck var e₁) (h₂: OccursCheck var e₁): OccursCheck var (.mult e₁ e₂)

  -- TODO: Weakening Lemma and Proper Substitution Equivalence

  namespace Term
    example: ¬((Command.while .true .skip).equiv .skip) := sorry
  end Term

  namespace Tactic
    example: ¬((Command.while .true .skip).equiv .skip) := by sorry
  end Tactic

  namespace Blended
    example: ¬((Command.while .true .skip).equiv .skip) := sorry
  end Blended

  /-
  ## Extended Exercise: Nondeterministic Imp
  -/

  namespace Havoc
    inductive Command: Type where
      | skip: Command
      | assign (id: String) (e: Arith): Command
      | seq (c₁ c₂: Command): Command
      | if (b: Logic) (c₁ c₂: Command): Command
      | while (b: Logic) (c: Command): Command
      | havoc (id: String): Command

    declare_syntax_cat havoc_cmd

    syntax:50 "skip" : havoc_cmd
    syntax:50 ident ":=" arith : havoc_cmd
    syntax:50 "‹" term "›" ":=" arith : havoc_cmd
    syntax:40 havoc_cmd ";" havoc_cmd : havoc_cmd
    syntax:50 "ite" "(" logic ")" "{" havoc_cmd "}" "else" "{" havoc_cmd "}" : havoc_cmd
    syntax:50 "while" "(" logic ")" "{" havoc_cmd "}" : havoc_cmd
    syntax:50 "havoc" ident : havoc_cmd
    syntax "(" havoc_cmd ")" : havoc_cmd
    syntax "‹" term "›" : havoc_cmd

    syntax "[Havoc|" havoc_cmd "]" : term

    macro_rules
      | `([Havoc| skip])                                => `(Command.skip)
      | `([Havoc| $id:ident := $e:arith])               => `(Command.assign $(Lean.quote (toString id.getId)) [Arith| $e])
      | `([Havoc| ‹$t:term› := $e:arith])           => `(Command.assign $(Lean.quote t) [Arith| $e])
      | `([Havoc| $x; $y])                              => `(Command.seq [Havoc| $x] [Havoc| $y])
      | `([Havoc| ite ( $c:logic ) { $t } else { $f }]) => `(Command.if [Logic| $c] [Havoc| $t] [Havoc| $f])
      | `([Havoc| while ( $c:logic ) { $b }])           => `(Command.while [Logic| $c] [Havoc| $b])
      | `([Havoc| havoc $id:ident ])                    => `(Command.havoc $(Lean.quote (toString id.getId)))
      | `([Havoc| ( $c )])                              => `([Havoc| $c])
      | `([Havoc| ‹$t:term› ])                      => pure t

    inductive CommandEval: Command → State → State → Prop where
      | skip {s: State}: CommandEval .skip s s
      | assign {s: State} {e: Arith} {n: Nat} {id: String} (h: e.eval s = n): CommandEval (.assign id e) s (s.update id n)
      | seq {c₁ c₂: Command} {s₁ s₂ s₃: State} (h₁: CommandEval c₁ s₁ s₂) (h₂: CommandEval c₂ s₂ s₃): CommandEval (.seq c₁ c₂) s₁ s₃
      | ifTrue {s₁ s₂: State} {c: Logic} {t f: Command} (h₁: c.eval s₁ = .true) (h₂: CommandEval t s₁ s₂): CommandEval (.if c t f) s₁ s₂
      | ifFalse {s₁ s₂: State} {c: Logic} {t f: Command} (h₁: c.eval s₁ = .false) (h₂: CommandEval f s₁ s₂): CommandEval (.if c t f) s₁ s₂
      | whileTrue {s₁ s₂ s₃: State} {c: Logic} {b: Command} (h₁: c.eval s₁ = .true) (h₂: CommandEval b s₁ s₂) (h₃: CommandEval (.while c b) s₂ s₃): CommandEval (.while c b) s₁ s₃
      | whileFalse {c: Logic} {s: State} {b: Command} (h₁: c.eval s = .false): CommandEval (.while c b) s s
      -- TODO: Define this properly
      | havoc {s₁ s₂: State} {id: String}: CommandEval (.havoc id) s₁ s₂

    notation s₁ "=[" c "]=>" s₂ => CommandEval c s₁ s₂

    def Command.equiv (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, (s₁ =[c₁]=> s₂) ↔ s₁ =[c₂]=> s₂

    infix:50 "≈" => Command.equiv

    private def xy := [Havoc| havoc X; havoc Y]
    private def yx := [Havoc| havoc Y; havoc X]
    private def copy := [Havoc| havoc X; Y := X]
    private def whileHavoc := [Havoc|
      while (!(X = 0)) {
        havoc X;
        X := X + 1
      }
    ]
    private def whileSkip := [Havoc| while (!(X = 0)) { skip }]
    private def havocHavoc := [Havoc|
      while (X ≠ 0) {
        havoc X;
        havoc Y
      }
    ]
    private def noHavoc := [Havoc| X := 0; Z := 1]

    namespace Term
      example: [State|] =[[Havoc| havoc X]]=> [State| X = 0] := sorry
      example: [State|] =[[Havoc| skip; havoc Z]]=> [State| Z = 42] := sorry

      example: xy ≈ yx ∨ ¬(xy ≈ yx) := sorry
      example: xy ≈ copy ∨ ¬(xy ≈ copy) := sorry

      example: whileHavoc ≈ whileSkip :=
        sorry
        where
          havoc_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(s₁ =[whileHavoc]=> s₂) := sorry
          skip_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(s₁ =[whileSkip]=> s₂) := sorry

      example: ¬(havocHavoc ≈ noHavoc) := sorry

      example: [Havoc| while (X ≠ 1) { havoc X }] ≈ [Havoc| X := 1] := sorry
    end Term

    namespace Tactic
      example: [State|] =[[Havoc| havoc X]]=> [State| X = 0] := by sorry
      example: [State|] =[[Havoc| skip; havoc Z]]=> [State| Z = 42] := by sorry

      example: xy ≈ yx ∨ ¬(xy ≈ yx) := by sorry
      example: xy ≈ copy ∨ ¬(xy ≈ copy) := by sorry

      example: whileHavoc ≈ whileSkip := by
        sorry
        where
          havoc_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(s₁ =[whileHavoc]=> s₂) := by sorry
          skip_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(s₁ =[whileSkip]=> s₂) := by sorry

      example: ¬(havocHavoc ≈ noHavoc) := by sorry

      example: [Havoc| while (X ≠ 1) { havoc X }] ≈ [Havoc| X := 1] := sorry
    end Tactic

    namespace Blended
      example: [State|] =[[Havoc| havoc X]]=> [State| X = 0] := sorry
      example: [State|] =[[Havoc| skip; havoc Z]]=> [State| Z = 42] := sorry

      example: xy ≈ yx ∨ ¬(xy ≈ yx) := sorry
      example: xy ≈ copy ∨ ¬(xy ≈ copy) := sorry

      example: whileHavoc ≈ whileSkip :=
        sorry
        where
          havoc_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(s₁ =[whileHavoc]=> s₂) := sorry
          skip_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(s₁ =[whileSkip]=> s₂) := sorry

      example: ¬(havocHavoc ≈ noHavoc) := sorry

      example: [Havoc| while (X ≠ 1) { havoc X }] ≈ [Havoc| X := 1] := sorry
    end Blended
  end Havoc

  /-
  ## Additional Exercises
  -/

  -- How is this different from "refines" above?
  @[reducible] def _root_.SoftwareFoundations.LogicalFoundations.Imp.Command.approx  (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, (s₁ =[c₁]=> s₂) → s₁ =[c₂]=> s₂

  private def approx_c₁ := [Imp| while (X ≠ 1) { X := X - 1}]
  private def approx_c₂ := [Imp| X := 1]

  private def approx_c₃: Command := sorry
  private def approx_c₄: Command := sorry

  private def approx_min: Command := sorry

  private def _root_.SoftwareFoundations.LogicalFoundations.Imp.Command.zProp (c: Command): Prop := sorry

  namespace Term
    example (id₁ id₂: String) (e₁ e₂: Arith) (h₁: OccursCheck id₁ e₁) (h₂: OccursCheck id₂ e₂): [Imp| ‹id₁› := ‹e₁›; ‹id₂› := ‹e₂›] ≈ [Imp| ‹id₂› := ‹e₂›; ‹id₁› := ‹e₁›] := sorry

    -- TODO: For loops in Imp

    example: ¬(approx_c₃.approx approx_c₄) ∧ ¬(approx_c₄.approx approx_c₃) := sorry
    example (c: Command): approx_min.approx c := sorry
    example (c₁ c₂: Command) (h₁: c₁.zProp) (h₂: c₁.approx c₂): c₂.zProp := sorry
  end Term

  namespace Tactic
    example (id₁ id₂: String) (e₁ e₂: Arith) (h₁: OccursCheck id₁ e₁) (h₂: OccursCheck id₂ e₂): [Imp| ‹id₁› := ‹e₁›; ‹id₂› := ‹e₂›] ≈ [Imp| ‹id₂› := ‹e₂›; ‹id₁› := ‹e₁›] := by sorry

    -- TODO: For loops in Imp

    example: ¬(approx_c₃.approx approx_c₄) ∧ ¬(approx_c₄.approx approx_c₃) := by sorry
    example (c: Command): approx_min.approx c := by sorry
    example (c₁ c₂: Command) (h₁: c₁.zProp) (h₂: c₁.approx c₂): c₂.zProp := by sorry
  end Tactic

  namespace Blended
    example (id₁ id₂: String) (e₁ e₂: Arith) (h₁: OccursCheck id₁ e₁) (h₂: OccursCheck id₂ e₂): [Imp| ‹id₁› := ‹e₁›; ‹id₂› := ‹e₂›] ≈ [Imp| ‹id₂› := ‹e₂›; ‹id₁› := ‹e₁›] := sorry

    -- TODO: For loops in Imp

    example: ¬(approx_c₃.approx approx_c₄) ∧ ¬(approx_c₄.approx approx_c₃) := sorry
    example (c: Command): approx_min.approx c := sorry
    example (c₁ c₂: Command) (h₁: c₁.zProp) (h₂: c₁.approx c₂): c₂.zProp := sorry
  end Blended
end SoftwareFoundations.ProgrammingLanguageFoundations.Equiv
