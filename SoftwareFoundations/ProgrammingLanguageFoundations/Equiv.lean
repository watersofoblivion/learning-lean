/-
# Program Equivalence
-/

import Mathlib.tactic.linarith

import «SoftwareFoundations».«LogicalFoundations».«Maps»
import «SoftwareFoundations».«LogicalFoundations».«Imp»

namespace SoftwareFoundations.ProgrammingLanguageFoundations.Equiv
  /-
  ## Behavioral Equivalence
  -/

  /-
  ### Definitions
  -/

  @[reducible] def _root_.Arith.equiv (a₁ a₂: Arith): Prop := ∀ s: State, a₁.eval s = a₂.eval s
  @[reducible] def _root_.Logic.equiv (l₁ l₂: Logic): Prop := ∀ s: State, l₁.eval s = l₂.eval s

  @[reducible] def _root_.Command.equiv (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, CommandEval c₁ s₁ s₂ ↔ CommandEval c₂ s₁ s₂
  @[reducible] def _root_.Command.refines (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, CommandEval c₁ s₁ s₂ → CommandEval c₂ s₁ s₂

  namespace Term
    example: (Arith.minus "X" "X").equiv (Arith.num 0) :=
      fun s =>
        calc (Arith.minus "X" "X").eval s
          _ = (s "X") - (s "X")    := rfl
          _ = 0                    := Nat.sub_self (s "X")
          _ = (Arith.num 0).eval s := rfl

    example: (Logic.eq (.minus "X" "X") 0).equiv .true :=
      fun s =>
        calc (Logic.eq (.minus "X" "X") 0).eval s
          _ = BEq.beq ((s "X") - (s "X")) 0 := rfl
          _ = BEq.beq 0 0                   := congrFun (congrArg BEq.beq (Nat.sub_self (s "X"))) 0
          _ = .true                         := rfl
  end Term

  namespace Tactic
    example: (Arith.minus "X" "X").equiv (Arith.num 0) := by
      unfold Arith.equiv
      intro s
      simp

    example: (Logic.eq (.minus "X" "X") 0).equiv .true := by
      unfold Logic.equiv
      intro s
      simp
      unfold Arith.eval
      rfl
  end Tactic

  namespace Blended
    example: (Arith.minus "X" "X").equiv (Arith.num 0) :=
      fun s =>
        calc (Arith.minus "X" "X").eval s
          _ = (s "X") - (s "X")    := by rfl
          _ = 0                    := by rw [Nat.sub_self]
          _ = (Arith.num 0).eval s := by rfl


    example: (Logic.eq (.minus "X" "X") 0).equiv .true :=
      fun s =>
        calc (Logic.eq (.minus "X" "X") 0).eval s
          _ = BEq.beq ((s "X") - (s "X")) 0 := by rfl
          _ = BEq.beq 0 0                   := by rw [Nat.sub_self]
          _ = .true                         := by rfl
  end Blended

  /-
  ### Simple Examples
  -/

  private def _root_.Logic.trueFalse (b: Logic) (s: State) (h₁: b.eval s = true) (h₂: b.eval s = false): α :=
    False.elim (by simp_all)

  namespace Term
    theorem Command.skip_left (c: Command): (Command.seq .skip c).equiv c
      | s₁, s₂ =>
        have mp: CommandEval (Command.seq .skip c) s₁ s₂ → CommandEval c s₁ s₂
          | .seq .skip h₂ => h₂
        have mpr: CommandEval c s₁ s₂ → CommandEval (Command.seq .skip c) s₁ s₂
          | .skip               => .seq .skip .skip
          | .assign h           => .seq .skip (.assign h)
          | .seq h₁ h₂          => .seq .skip (.seq h₁ h₂)
          | .ifTrue h₁ h₂       => .seq .skip (.ifTrue h₁ h₂)
          | .ifFalse h₁ h₂      => .seq .skip (.ifFalse h₁ h₂)
          | .whileTrue h₁ h₂ h₃ => .seq .skip (.whileTrue h₁ h₂ h₃)
          | .whileFalse h₁      => .seq .skip (.whileFalse h₁)
        ⟨mp, mpr⟩

    theorem Command.skip_right (c: Command): (Command.seq c .skip).equiv c
      | s₁, s₂ =>
        have mp: CommandEval (Command.seq c .skip) s₁ s₂ → CommandEval c s₁ s₂
          | .seq h₁ .skip => h₁
        have mpr: CommandEval c s₁ s₂ → CommandEval (Command.seq c .skip) s₁ s₂
          | .skip               => .seq .skip .skip
          | .assign h           => .seq (.assign h) .skip
          | .seq h₁ h₂          => .seq (.seq h₁ h₂) .skip
          | .ifTrue h₁ h₂       => .seq (.ifTrue h₁ h₂) .skip
          | .ifFalse h₁ h₂      => .seq (.ifFalse h₁ h₂) .skip
          | .whileTrue h₁ h₂ h₃ => .seq (.whileTrue h₁ h₂ h₃) .skip
          | .whileFalse h₁      => .seq (.whileFalse h₁) .skip
        ⟨mp, mpr⟩

    example {t f: Command}: (Command.if .true t f).equiv t
      | s₁, s₂ =>
        have mp: CommandEval (.if .true t f) s₁ s₂ → CommandEval t s₁ s₂
          | .ifTrue _ h₂ => h₂
          | .ifFalse h₁ _ => Logic.true.trueFalse s₁ rfl h₁
        have mpr: CommandEval t s₁ s₂ → CommandEval (.if .true t f) s₁ s₂
          | .skip               => .ifTrue rfl .skip
          | .assign h           => .ifTrue rfl (.assign h)
          | .seq h₁ h₂          => .ifTrue rfl (.seq h₁ h₂)
          | .ifTrue h₁ h₂       => .ifTrue rfl (.ifTrue h₁ h₂)
          | .ifFalse h₁ h₂      => .ifTrue rfl (.ifFalse h₁ h₂)
          | .whileTrue h₁ h₂ h₃ => .ifTrue rfl (.whileTrue h₁ h₂ h₃)
          | .whileFalse h       => .ifTrue rfl (.whileFalse h)
        ⟨mp, mpr⟩

    theorem Command.if_true (b: Logic) (c₁ c₂: Command) (h: b.equiv .true): (Command.if b c₁ c₂).equiv c₁
      | s₁, s₂ =>
        have tru: b.eval s₁ = Logic.true.eval s₁ := h _
        have mp: CommandEval (.if b c₁ c₂) s₁ s₂ → CommandEval c₁ s₁ s₂
          | .ifTrue _ h₂ => h₂
          | .ifFalse h₁ _ => b.trueFalse s₁ tru h₁
        have mpr: CommandEval c₁ s₁ s₂ → CommandEval (.if b c₁ c₂) s₁ s₂
          | .skip               => .ifTrue tru .skip
          | .assign h₁          => .ifTrue tru (.assign h₁)
          | .seq h₁ h₂          => .ifTrue tru (.seq h₁ h₂)
          | .ifTrue h₁ h₂       => .ifTrue tru (.ifTrue h₁ h₂)
          | .ifFalse h₁ h₂      => .ifTrue tru (.ifFalse h₁ h₂)
          | .whileTrue h₁ h₂ h₃ => .ifTrue tru (.whileTrue h₁ h₂ h₃)
          | .whileFalse h₁      => .ifTrue tru (.whileFalse h₁)
        ⟨mp, mpr⟩

    theorem Command.if_false (b: Logic) (c₁ c₂: Command) (h: b.equiv .false): (Command.if b c₁ c₂).equiv c₂
      | s₁, s₂ =>
        have fls: b.eval s₁ = Logic.false.eval s₁ := h _
        have mp: CommandEval (.if b c₁ c₂) s₁ s₂ → CommandEval c₂ s₁ s₂
          | .ifTrue h₁ _ => b.trueFalse s₁ h₁ fls
          | .ifFalse _ h₂ => h₂
        have mpr: CommandEval c₂ s₁ s₂ → CommandEval (.if b c₁ c₂) s₁ s₂
          | .skip               => .ifFalse fls .skip
          | .assign h₁          => .ifFalse fls (.assign h₁)
          | .seq h₁ h₂          => .ifFalse fls (.seq h₁ h₂)
          | .ifTrue h₁ h₂       => .ifFalse fls (.ifTrue h₁ h₂)
          | .ifFalse h₁ h₂      => .ifFalse fls (.ifFalse h₁ h₂)
          | .whileTrue h₁ h₂ h₃ => .ifFalse fls (.whileTrue h₁ h₂ h₃)
          | .whileFalse h₁      => .ifFalse fls (.whileFalse h₁)
        ⟨mp, mpr⟩

    theorem Command.if_swap (b: Logic) (c₁ c₂: Command): (Command.if b c₁ c₂).equiv (Command.if (.not b) c₂ c₁)
      | s₁, s₂ =>
        have mp: CommandEval (.if b c₁ c₂) s₁ s₂ → CommandEval (.if (.not b) c₂ c₁) s₁ s₂ := sorry
        have mpr: CommandEval (.if (.not b) c₂ c₁) s₁ s₂ → CommandEval (.if b c₁ c₂) s₁ s₂ := sorry
        ⟨mp, mpr⟩

    theorem Command.while_false (c: Logic) (b: Command) (h: c.equiv .false): (Command.while c b).equiv Command.skip
      | s₁, s₂ =>
        have fls: c.eval s₁ = Logic.false.eval s₁ := h _
        have mp: CommandEval (.while c b) s₁ s₂ → CommandEval .skip s₁ s₂
          | .whileTrue h₁ _ _=> c.trueFalse s₁ h₁ fls
          | .whileFalse _ => .skip
        have mpr: CommandEval .skip s₁ s₂ → CommandEval (.while c b) s₁ s₂
          | .skip => .whileFalse fls
        ⟨mp, mpr⟩

    theorem Command.while_true (c: Logic) (b: Command) (h: c.equiv .true): (Command.while c b).equiv (Command.while .true Command.skip)
      | s₁, s₂ =>
        have tru: c.eval s₁ = Logic.true.eval s₁ := h _
        have mp: CommandEval (.while c b) s₁ s₂ → CommandEval (.while .true .skip) s₁ s₂
          | .whileTrue h₁ _ _ => sorry -- .whileTrue_ _
          | .whileFalse h₁ => c.trueFalse s₁ tru h₁
        have mpr: CommandEval (.while .true .skip) s₁ s₂ → CommandEval (.while c b) s₁ s₂
          | .whileTrue h₁ h₂ h₃ => sorry -- .whileTrue tru _ _
          | .whileFalse h₁ => Logic.true.trueFalse s₂ rfl h₁
        ⟨mp, mpr⟩
      where
        nonterm (c: Logic) (b: Command) (s₁ s₂: State) (h: c.equiv .true): ¬(CommandEval (.while c b) s₁ s₂)
          | .whileTrue h₁ _ _ =>
              -- have contra: ¬ CommandEval (.while c b) s₁ s₂ := sorry
              -- absurd hn contra
              -- have hh := nonterm _ b u v h
              sorry
              -- False.elim hh
              -- sorry
          | .whileFalse h₁ => c.trueFalse s₁ (h _) h₁

    theorem Command.loop_unrolling (c: Logic) (b: Command): (Command.while c b).equiv (Command.if c (Command.seq b (Command.while c b)) .skip)
      | s₁, s₂ =>
        have mp: CommandEval (.while c b) s₁ s₂ → CommandEval (.if c (.seq b (.while c b)) .skip) s₁ s₂ := sorry
        have mpr: CommandEval (.if c (.seq b (.while c b)) .skip) s₁ s₂ → CommandEval (.while c b) s₁ s₂ := sorry
        ⟨mp, mpr⟩

    theorem Command.seq_assoc (c₁ c₂ c₃: Command): (Command.seq (Command.seq c₁ c₂) c₃).equiv (Command.seq c₁ (Command.seq c₂ c₃))
      | s₁, s₂ =>
        have mp: CommandEval (.seq (.seq c₁ c₂) c₃) s₁ s₂ → CommandEval (.seq c₁ (.seq c₂ c₃)) s₁ s₂
          | .seq (.seq h₁ h₂) h₃ => .seq h₁ (.seq h₂ h₃)
        have mpr: CommandEval (.seq c₁ (.seq c₂ c₃)) s₁ s₂ → CommandEval (.seq (.seq c₁ c₂) c₃) s₁ s₂
          | .seq h₁ (.seq h₂ h₃) => .seq (.seq h₁ h₂) h₃
        ⟨mp, mpr⟩

    theorem Command.identity_assignment (id: String): (Command.assign id (.ident id)).equiv Command.skip
      | s₁, s₂ =>
        -- Should use Maps.TotalMap.updateSame
        have mp: CommandEval (.assign id id) s₁ s₂ → CommandEval .skip s₁ s₂
          | .assign h => sorry
        have mpr: CommandEval .skip s₁ s₂ → CommandEval (.assign id id) s₁ s₂
          | .skip => sorry
        ⟨mp, mpr⟩

    theorem Command.assign_arith_equiv (id: String) (e: Arith) (h: (id: Arith).equiv e): Command.skip.equiv (Command.assign id e)
      | s₁, s₂ =>
        have mp: CommandEval .skip s₁ s₂ → CommandEval (.assign id e) s₁ s₂
          | .skip => sorry
        have mpr: CommandEval (.assign id e) s₁ s₂ → CommandEval .skip s₁ s₂
          | .assign _ => sorry
        ⟨mp, mpr⟩
  end Term

  namespace Tactic
    @[scoped simp]
    theorem Command.skip_left (c: Command): (Command.seq .skip c).equiv c := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .seq h₁ _ => cases h₁; assumption
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
    theorem Command.skip_right (c: Command): (Command.seq c .skip).equiv c := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .seq _ h₂ => cases h₂; assumption
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

    example {t f: Command}: (Command.if .true t f).equiv t := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .ifTrue _ _ => assumption
        | .ifFalse _ _ => contradiction
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
    theorem Command.if_true (b: Logic) (c₁ c₂: Command) (h: b.equiv .true): (Command.if b c₁ c₂).equiv c₁ := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .ifTrue _ _ => assumption
        | .ifFalse h₃ _ =>
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
    theorem Command.if_false (b: Logic) (c₁ c₂: Command) (h: b.equiv .false): (Command.if b c₁ c₂).equiv c₂ := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .ifTrue h₁ _ =>
            rw [h s₁] at h₁
            contradiction
        | .ifFalse _ _ => assumption
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

    theorem Command.if_swap (b: Logic) (c₁ c₂: Command): (Command.if b c₁ c₂).equiv (Command.if (.not b) c₂ c₁) := by
      intro s₁ s₂
      apply Iff.intro
      · sorry
      · sorry

    @[scoped simp]
    theorem Command.while_false (c: Logic) (b: Command) (h: c.equiv .false): (Command.while c b).equiv Command.skip := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .whileTrue h₁ _ _ =>
          rw [h s₁] at h₁
          contradiction
        | .whileFalse _ => apply CommandEval.skip
      · intro
        | .skip =>
            apply CommandEval.whileFalse
            · rw [h s₁]

    @[scoped simp]
    theorem Command.while_true (c: Logic) (b: Command) (h: c.equiv .true): (Command.while c b).equiv (Command.while .true Command.skip) := by
      intro s₁ s₂
      apply Iff.intro
      · sorry
      · sorry
      where
        nonterm (c: Logic) (b: Command) (s₁ s₂: State) (h: c.equiv .true): ¬(CommandEval (.while c b) s₁ s₂) := by
          intro
          | .whileTrue _ _ _ => sorry
          | .whileFalse _ => simp_all

    theorem Command.loop_unrolling (c: Logic) (b: Command): (Command.while c b).equiv (Command.if c (Command.seq b (Command.while c b)) .skip) := by
      intro s₁ s₂
      apply Iff.intro
      · sorry
      · sorry

    theorem Command.seq_assoc (c₁ c₂ c₂: Command): (Command.seq (Command.seq c₁ c₂) c₃).equiv (Command.seq c₁ (Command.seq c₂ c₃)) := by
      intro s₁ s₂
      apply Iff.intro
      · intro
        | .seq h₁ _ =>
          cases h₁
          · apply CommandEval.seq
            <;> (try apply CommandEval.seq
                 repeat assumption)
      · intro
        | .seq _ h₂ =>
          cases h₂
          · apply CommandEval.seq
            <;> (try apply CommandEval.seq
                 repeat assumption)

    @[scoped simp]
    theorem Command.identity_assignment (id: String): (Command.assign id (.ident id)).equiv Command.skip := by
      intro s₁ s₂
      apply Iff.intro
      · sorry
      · sorry

    theorem Command.assign_arith_equiv (id: String) (e: Arith) (h₁: (id: Arith).equiv e): Command.skip.equiv (Command.assign id e) := by
      unfold Command.equiv
      intro s₁ s₂
      apply Iff.intro
      · sorry
      · sorry
  end Tactic

  namespace Blended
    @[scoped simp]
    theorem Command.skip_left (c: Command): (Command.seq .skip c).equiv c
      | s₁, s₂ =>
        have mp: CommandEval (Command.seq .skip c) s₁ s₂ → CommandEval c s₁ s₂
          | .seq .skip h₂ => h₂
        have mpr: CommandEval c s₁ s₂ → CommandEval (Command.seq .skip c) s₁ s₂
          | .skip               => .seq .skip .skip
          | .assign h           => .seq .skip (.assign h)
          | .seq h₁ h₂          => .seq .skip (.seq h₁ h₂)
          | .ifTrue h₁ h₂       => .seq .skip (.ifTrue h₁ h₂)
          | .ifFalse h₁ h₂      => .seq .skip (.ifFalse h₁ h₂)
          | .whileTrue h₁ h₂ h₃ => .seq .skip (.whileTrue h₁ h₂ h₃)
          | .whileFalse h₁      => .seq .skip (.whileFalse h₁)
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.skip_right (c: Command): (Command.seq c .skip).equiv c
      | s₁, s₂ =>
        have mp: CommandEval (Command.seq c .skip) s₁ s₂ → CommandEval c s₁ s₂
          | .seq h₁ .skip => h₁
        have mpr: CommandEval c s₁ s₂ → CommandEval (Command.seq c .skip) s₁ s₂
          | .skip               => .seq .skip .skip
          | .assign h           => .seq (.assign h) .skip
          | .seq h₁ h₂          => .seq (.seq h₁ h₂) .skip
          | .ifTrue h₁ h₂       => .seq (.ifTrue h₁ h₂) .skip
          | .ifFalse h₁ h₂      => .seq (.ifFalse h₁ h₂) .skip
          | .whileTrue h₁ h₂ h₃ => .seq (.whileTrue h₁ h₂ h₃) .skip
          | .whileFalse h₁      => .seq (.whileFalse h₁) .skip
        ⟨mp, mpr⟩

    @[scoped simp]
    example {t f: Command}: (Command.if .true t f).equiv t
      | s₁, s₂ =>
        have mp: CommandEval (.if .true t f) s₁ s₂ → CommandEval t s₁ s₂
          | .ifTrue _ h₂ => h₂
          | .ifFalse h₁ _ => Logic.true.trueFalse s₁ rfl h₁
        have mpr: CommandEval t s₁ s₂ → CommandEval (.if .true t f) s₁ s₂
          | .skip               => .ifTrue rfl .skip
          | .assign h           => .ifTrue rfl (.assign h)
          | .seq h₁ h₂          => .ifTrue rfl (.seq h₁ h₂)
          | .ifTrue h₁ h₂       => .ifTrue rfl (.ifTrue h₁ h₂)
          | .ifFalse h₁ h₂      => .ifTrue rfl (.ifFalse h₁ h₂)
          | .whileTrue h₁ h₂ h₃ => .ifTrue rfl (.whileTrue h₁ h₂ h₃)
          | .whileFalse h       => .ifTrue rfl (.whileFalse h)
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.if_true (b: Logic) (c₁ c₂: Command) (h: b.equiv .true): (Command.if b c₁ c₂).equiv c₁
      | s₁, s₂ =>
        have tru: b.eval s₁ = Logic.true.eval s₁ := h _
        have mp: CommandEval (.if b c₁ c₂) s₁ s₂ → CommandEval c₁ s₁ s₂
          | .ifTrue _ h₂ => h₂
          | .ifFalse h₁ _ => b.trueFalse s₁ tru h₁
        have mpr: CommandEval c₁ s₁ s₂ → CommandEval (.if b c₁ c₂) s₁ s₂
          | .skip               => .ifTrue tru .skip
          | .assign h₁          => .ifTrue tru (.assign h₁)
          | .seq h₁ h₂          => .ifTrue tru (.seq h₁ h₂)
          | .ifTrue h₁ h₂       => .ifTrue tru (.ifTrue h₁ h₂)
          | .ifFalse h₁ h₂      => .ifTrue tru (.ifFalse h₁ h₂)
          | .whileTrue h₁ h₂ h₃ => .ifTrue tru (.whileTrue h₁ h₂ h₃)
          | .whileFalse h₁      => .ifTrue tru (.whileFalse h₁)
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.if_false (b: Logic) (c₁ c₂: Command) (h: b.equiv .false): (Command.if b c₁ c₂).equiv c₂
      | s₁, s₂ =>
        have fls: b.eval s₁ = Logic.false.eval s₁ := h _
        have mp: CommandEval (.if b c₁ c₂) s₁ s₂ → CommandEval c₂ s₁ s₂
          | .ifTrue h₁ _ => b.trueFalse s₁ h₁ fls
          | .ifFalse _ h₂ => h₂
        have mpr: CommandEval c₂ s₁ s₂ → CommandEval (.if b c₁ c₂) s₁ s₂
          | .skip               => .ifFalse fls .skip
          | .assign h₁          => .ifFalse fls (.assign h₁)
          | .seq h₁ h₂          => .ifFalse fls (.seq h₁ h₂)
          | .ifTrue h₁ h₂       => .ifFalse fls (.ifTrue h₁ h₂)
          | .ifFalse h₁ h₂      => .ifFalse fls (.ifFalse h₁ h₂)
          | .whileTrue h₁ h₂ h₃ => .ifFalse fls (.whileTrue h₁ h₂ h₃)
          | .whileFalse h₁      => .ifFalse fls (.whileFalse h₁)
        ⟨mp, mpr⟩

    theorem Command.if_swap (b: Logic) (c₁ c₂: Command): (Command.if b c₁ c₂).equiv (Command.if (.not b) c₂ c₁) := by sorry

    @[scoped simp]
    theorem Command.while_false (c: Logic) (b: Command) (h: c.equiv .false): (Command.while c b).equiv Command.skip
      | s₁, s₂ =>
        have fls: c.eval s₁ = Logic.false.eval s₁ := h _
        have mp: CommandEval (.while c b) s₁ s₂ → CommandEval .skip s₁ s₂
          | .whileTrue h₁ _ _=> c.trueFalse s₁ h₁ fls
          | .whileFalse _ => .skip
        have mpr: CommandEval .skip s₁ s₂ → CommandEval (.while c b) s₁ s₂
          | .skip => .whileFalse fls
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.while_true (c: Logic) (b: Command) (h: c.equiv .true): (Command.while c b).equiv (Command.while .true Command.skip)
      | s₁, s₂ =>
        have tru: c.eval s₁ = Logic.true.eval s₁ := h _
        sorry

    theorem Command.loop_unrolling (c: Logic) (b: Command): (Command.while c b).equiv (Command.if c (Command.seq b (Command.while c b)) .skip) := by sorry

    theorem Command.seq_assoc (c₁ c₂ c₃: Command): (Command.seq (Command.seq c₁ c₂) c₃).equiv (Command.seq c₁ (Command.seq c₂ c₃))
      | s₁, s₂ =>
        have mp: CommandEval (.seq (.seq c₁ c₂) c₃) s₁ s₂ → CommandEval (.seq c₁ (.seq c₂ c₃)) s₁ s₂
          | .seq (.seq h₁ h₂) h₃ => .seq h₁ (.seq h₂ h₃)
        have mpr: CommandEval (.seq c₁ (.seq c₂ c₃)) s₁ s₂ → CommandEval (.seq (.seq c₁ c₂) c₃) s₁ s₂
          | .seq h₁ (.seq h₂ h₃) => .seq (.seq h₁ h₂) h₃
        ⟨mp, mpr⟩

    @[scoped simp]
    theorem Command.identity_assignment (id: String): (Command.assign id (.ident id)).equiv Command.skip := by sorry

    theorem Command.assign_arith_equiv (id: String) (e: Arith) (h₁: (id: Arith).equiv e): Command.skip.equiv (Command.assign id e) := by sorry
  end Blended

  section
    private def a: Command :=
      .while (.gt "X" 0)
        (.assign "X" ("X" + 1))

    private def b: Command :=
      .seq
        (.if (.eq "X" 0)
          (.seq
            (.assign "X" ("X" + 1))
            (.assign "Y" 1))
          (.assign "Y" 0))
        (.seq
          (.assign "X" ("X" - "Y"))
          (.assign "Y" 0))

    private def c: Command :=
      .skip

    private def d: Command :=
      .while (.neq "X" 0)
        (.assign "X" ("X" * "Y" + 1))

    private def e: Command :=
      .assign "Y" 0

    private def f: Command :=
      .seq
        (.assign "Y" ("X" + 1))
        (.while (.neq "X" "Y")
          (.assign "Y" ("X" + 1)))

    private def g: Command :=
      .while .true .skip

    private def h: Command :=
      .while (.neq "X" "X")
        (.assign "X" ("X" + 1))

    private def i: Command :=
      .while (.neq "X" "Y")
        (.assign "X" ("Y" + 1))

    private def equiv_classes: List (List Command) := []
  end

  /-
  ## Properties of Behavioral Equivalence
  -/

  /-
  ### Behavioral Equivalence is an Equivalence
  -/

  namespace Term
    theorem Arith.equiv.refl (e: Arith): e.equiv e
      | _ => Eq.refl (e.eval _)
    theorem Arith.equiv.symm (e₁ e₂: Arith) (h: e₁.equiv e₂): e₂.equiv e₁
      | _ => Eq.symm (h _)
    theorem Arith.equiv.trans (e₁ e₂ e₃: Arith) (h₁: e₁.equiv e₂) (h₂: e₂.equiv e₃): e₁.equiv e₃
      | _ => Eq.trans (h₁ _) (h₂ _)

    theorem Logic.equiv.refl (b: Logic): b.equiv b
      | _ => Eq.refl (b.eval _)
    theorem Logic.equiv.symm (b₁ b₂: Logic) (h: b₁.equiv b₂): b₂.equiv b₁
      | _ => Eq.symm (h _)
    theorem Logic.equiv.trans (b₁ b₂ b₃: Logic) (h₁: b₁.equiv b₂) (h₂: b₂.equiv b₃): b₁.equiv b₃
      | _ => Eq.trans (h₁ _) (h₂ _)

    theorem Command.equiv.refl (c: Command): c.equiv c
      | _, _ => Iff.refl (CommandEval c _ _)
    theorem Command.equiv.symm (c₁ c₂: Command) (h: c₁.equiv c₂): c₂.equiv c₁
      | _, _ => Iff.symm (h _ _)
    theorem Command.equiv.trans (c₁ c₂ c₃: Command) (h₁: c₁.equiv c₂) (h₂: c₂.equiv c₃): c₁.equiv c₃
      | _, _ => Iff.trans (h₁ _ _) (h₂ _ _)
  end Term

  namespace Tactic
    theorem Arith.equiv.refl (e: Arith): e.equiv e := by
      intro s
      rfl
    theorem Arith.equiv.symm (e₁ e₂: Arith) (h: e₁.equiv e₂): e₂.equiv e₁ := by
      intro s
      rw [h s]
    theorem Arith.equiv.trans (e₁ e₂ e₃: Arith) (h₁: e₁.equiv e₂) (h₂: e₂.equiv e₃): e₁.equiv e₃ := by
      intro s
      rw [h₁ s, h₂ s]

    theorem Logic.equiv.refl (b: Logic): b.equiv b := by
      intro s
      rfl
    theorem Logic.equiv.symm (b₁ b₂: Logic) (h: b₁.equiv b₂): b₂.equiv b₁ := by
      intro s
      rw [h s]
    theorem Logic.equiv.trans (b₁ b₂ b₃: Logic) (h₁: b₁.equiv b₂) (h₂: b₂.equiv b₃): b₁.equiv b₃ := by
      intro s
      rw [h₁ s, h₂ s]

    theorem Command.equiv.refl (c: Command): c.equiv c := by
      intro s₁ s₂
      rfl
    theorem Command.equiv.symm (c₁ c₂: Command) (h: c₁.equiv c₂): c₂.equiv c₁ := by
      intro s₁ s₂
      rw [h s₁ s₂]
    theorem Command.equiv.trans (c₁ c₂ c₃: Command) (h₁: c₁.equiv c₂) (h₂: c₂.equiv c₃): c₁.equiv c₃ := by
      intro s₁ s₂
      rw [h₁ s₁ s₂, h₂ s₁ s₂]
  end Tactic

  namespace Blended
    theorem Arith.equiv.refl (e: Arith): e.equiv e
      | _ => Eq.refl (e.eval _)
    theorem Arith.equiv.symm (e₁ e₂: Arith) (h: e₁.equiv e₂): e₂.equiv e₁
      | _ => Eq.symm (h _)
    theorem Arith.equiv.trans (e₁ e₂ e₃: Arith) (h₁: e₁.equiv e₂) (h₂: e₂.equiv e₃): e₁.equiv e₃
      | _ => Eq.trans (h₁ _) (h₂ _)

    theorem Logic.equiv.refl (b: Logic): b.equiv b
      | _ => Eq.refl (b.eval _)
    theorem Logic.equiv.symm (b₁ b₂: Logic) (h: b₁.equiv b₂): b₂.equiv b₁
      | _ => Eq.symm (h _)
    theorem Logic.equiv.trans (b₁ b₂ b₃: Logic) (h₁: b₁.equiv b₂) (h₂: b₂.equiv b₃): b₁.equiv b₃
      | _ => Eq.trans (h₁ _) (h₂ _)

    theorem Command.equiv.refl (c: Command): c.equiv c
      | _, _ => Iff.refl (CommandEval c _ _)
    theorem Command.equiv.symm (c₁ c₂: Command) (h: c₁.equiv c₂): c₂.equiv c₁
      | _, _ => Iff.symm (h _ _)
    theorem Command.equiv.trans (c₁ c₂ c₃: Command) (h₁: c₁.equiv c₂) (h₂: c₂.equiv c₃): c₁.equiv c₃
      | _, _ => Iff.trans (h₁ _ _) (h₂ _ _)
  end Blended

  /-
  ### Behavioral Equivalence is a Congruence
  -/

  private def congr_prog₁: Command :=
    .seq
      (.assign "X" 0)
      (.if (.eq "X" 0)
        (.assign "Y" 0)
        (.assign "Y" 42))
  private def congr_prog₂: Command :=
    .seq
      (.assign "X" 0)
      (.if (.eq "X" 0)
        (.assign "Y" ("X" - "X"))
        (.assign "Y" 42))

  namespace Term
    theorem Command.skip.congr: Command.skip.equiv .skip
      | _, _ => Iff.refl _
    theorem Command.assign.congr (id: String) (e₁ e₂: Arith) (h: e₁.equiv e₂): (Command.assign id e₁).equiv (.assign id e₂)
      | s₁, s₂ => sorry
    theorem Command.seq.congr (c₁ c₂ c₃ c₄: Command) (h₁: c₁.equiv c₃) (h₂: c₂.equiv c₄): (Command.seq c₁ c₃).equiv (.seq c₂ c₄)
      | s₁, s₂ => sorry
    theorem Command.if.congr (c₁ c₂: Logic) (t₁ t₂ f₁ f₂: Command) (h₁: c₁.equiv c₂) (h₂: t₁.equiv t₂) (h₃: f₁.equiv f₁): (Command.if c₁ t₁ f₁).equiv (.if c₂ t₂ f₂)
      | s₁, s₂ => sorry

    example: congr_prog₁.equiv congr_prog₂ := sorry
  end Term

  namespace Tactic
    theorem Command.skip.congr: Command.skip.equiv .skip := by sorry
    theorem Command.assign.congr (id: String) (e₁ e₂: Arith) (h: e₁.equiv e₂): (Command.assign id e₁).equiv (.assign id e₂) := by sorry
    theorem Command.seq.congr (c₁ c₂ c₃ c₄: Command) (h₁: c₁.equiv c₃) (h₂: c₂.equiv c₄): (Command.seq c₁ c₃).equiv (.seq c₂ c₄) := by sorry
    theorem Command.if.congr (c₁ c₂: Logic) (t₁ t₂ f₁ f₂: Command) (h₁: c₁.equiv c₂) (h₂: t₁.equiv t₂) (h₃: f₁.equiv f₁): (Command.if c₁ t₁ f₁).equiv (.if c₂ t₂ f₂) := by sorry

    example: congr_prog₁.equiv congr_prog₂ := by sorry
  end Tactic

  namespace Blended
    theorem Command.skip.congr: Command.skip.equiv .skip := sorry
    theorem Command.assign.congr (id: String) (e₁ e₂: Arith) (h: e₁.equiv e₂): (Command.assign id e₁).equiv (.assign id e₂) := sorry
    theorem Command.seq.congr (c₁ c₂ c₃ c₄: Command) (h₁: c₁.equiv c₃) (h₂: c₂.equiv c₄): (Command.seq c₁ c₃).equiv (.seq c₂ c₄) := sorry
    theorem Command.if.congr (c₁ c₂: Logic) (t₁ t₂ f₁ f₂: Command) (h₁: c₁.equiv c₂) (h₂: t₁.equiv t₂) (h₃: f₁.equiv f₁): (Command.if c₁ t₁ f₁).equiv (.if c₂ t₂ f₂) := sorry

    example: congr_prog₁.equiv congr_prog₂ := sorry
  end Blended

  /-
  ## Program Transformations
  -/

  def Arith.transform_sound (t: Arith → Arith): Prop := ∀ e: Arith, e.equiv (t e)
  def Logic.transform_sound (t: Logic → Logic): Prop := ∀ b: Logic, b.equiv (t b)
  def Command.transform_sound (t: Command → Command): Prop := ∀ c: Command, c.equiv (t c)

  /-
  ### Constant Folding Optimization
  -/

  @[reducible]
  def _root_.Arith.constFold: _root_.Arith → _root_.Arith
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

  example: (((1: Arith) + 2) * "X").constFold = 3 * "X" := rfl
  example: ("X" - (((0: Arith) * 6) + "Y")).constFold = "X" - (0 + "Y") := rfl

  @[reducible]
  def _root_.Logic.constFold: _root_.Logic → _root_.Logic
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

  example: (Logic.and .true (.not (.false && .true))).constFold = .true := rfl
  example: (Logic.and (.eq "X" "Y") (.eq 0 (2 - (1 + 1)))).constFold = .and (.eq "X" "Y") .true := rfl

  @[reducible]
  def _root_.Command.constFold: Command → Command
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
      let b: Command := b.constFold
      match c.constFold with
        | .true => .while .true .skip
        | .false => .skip
        | c => .while c b

  example:
    (Command.seq
      (.assign "X" (4 + 5))
      (Command.seq
        (.assign "Y" ("X" - 3))
        (Command.seq
          (.if (.eq ("X" - "Y") (2 + 4))
            .skip
            (.assign "Y" 0))
          (Command.seq
            (.if (.le 0 (4 - (2 + 1)))
              (.assign "Y" 0)
              .skip)
            (.while (.eq "Y" 0)
              (.assign "X" ("X" + 1))))))).constFold
    =
    Command.seq
    (.assign "X" 9)
    (Command.seq
      (.assign "Y" ("X" - 3))
      (Command.seq
        (.if (.eq ("X" - "Y") 6)
          .skip
          (.assign "Y" 0))
        (Command.seq
          (.assign "Y" 0)
          (.while (.eq "Y" 0)
            (.assign "X" ("X" + 1))))))
    := rfl

  /-
  ### Soundness of Constant Folding
  -/

  namespace Term
    theorem Arith.constFold.sound: Arith.transform_sound Arith.constFold := sorry
    theorem Logic.constFold.sound: Logic.transform_sound Logic.constFold := sorry
    theorem Command.constFold.sound: Command.transform_sound Command.constFold := sorry
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
  def _root_.Arith.opt0Plus: Arith → Arith
    | .plus (.num 0) e₂ => e₂.opt0Plus
    | .plus e₁ e₂ => .plus e₁.opt0Plus e₂.opt0Plus
    | .minus e₁ e₂ => .minus e₁.opt0Plus e₂.opt0Plus
    | .mult e₁ e₂ => .mult e₁.opt0Plus e₂.opt0Plus
    | e => e

  @[reducible]
  def _root_.Logic.opt0Plus: Logic → Logic
    | .eq e₁ e₂ => .eq e₁.opt0Plus e₂.opt0Plus
    | .neq e₁ e₂ => .neq e₁.opt0Plus e₂.opt0Plus
    | .le e₁ e₂ => .le e₁.opt0Plus e₂.opt0Plus
    | .gt e₁ e₂ => .gt e₁.opt0Plus e₂.opt0Plus
    | .not b => .not (opt0Plus b)
    | .and b₁ b₂ => .and (opt0Plus b₁) (opt0Plus b₂)
    | b => b

  @[reducible]
  def _root_.Command.opt0Plus: Command → Command
    | .assign id e => .assign id e.opt0Plus
    | .seq c₁ c₂ => .seq (opt0Plus c₁) (opt0Plus c₂)
    | .if c t f => .if c.opt0Plus (opt0Plus t) (opt0Plus f)
    | .while c b => .while c.opt0Plus (opt0Plus b)
    | c => c

  example: (Command.while (.neq "X" 0) (.assign "X" (0 + "X" - 1))).opt0Plus = .while (.neq "X" 0) (.assign "X" ("X" - 1)) := rfl

  namespace Term
    theorem Arith.opt0Plus.sound: Arith.transform_sound Arith.opt0Plus := sorry
      -- | .num _ => fun s => rfl
      -- | .ident _ => fun s => rfl
      -- | .plus (.num 0) e₂, s =>
      --   have ih₁ := sound (.num 0) s
      --   have ih₂ := sound e₂ s
      --   calc (Arith.plus (.num 0) e₂).eval s
      --     _ = (Arith.num 0).eval s + e₂.eval s                       := rfl
      --     _ = (Arith.num 0).opt0Plus.eval s + e₂.opt0Plus.eval s     := congr (congrArg Nat.add ih₁) ih₂
      --     _ = (Arith.plus (Arith.num 0).opt0Plus e₂.opt0Plus).eval s := rfl
      --     _ = (Arith.plus (Arith.num 0) e₂).opt0Plus.eval s          := by simp -- congrArg (Arith.eval s) rfl -- TODO: Remove Tactic Block
      --     _ = e₂.opt0Plus.eval s                                     := rfl
      -- | .plus (.num (.succ n)) e₂ => fun s =>
      --   have ih₁ := sound (.num (.succ n)) s
      --   have ih₂ := sound e₂ s
      --   calc (Arith.plus (.num (.succ n)) e₂).eval s
      --     _ = (Arith.num (.succ n)).eval s + e₂.eval s                   := rfl
      --     _ = (Arith.num (.succ n)).opt0Plus.eval s + e₂.opt0Plus.eval s := congr (congrArg Nat.add ih₁) ih₂
      --     _ = (Arith.plus (.num (.succ n)) e₂).opt0Plus.eval s           := rfl
      -- | .minus e₁ e₂ => fun s =>
      --   have ih₁ := sound e₁ s
      --   have ih₂ := sound e₂ s
      --   calc (Arith.minus e₁ e₂).eval s
      --     _ = e₁.eval s - e₂.eval s                   := rfl
      --     _ = e₁.opt0Plus.eval s - e₂.opt0Plus.eval s := congr (congrArg Nat.sub ih₁) ih₂
      --     _ = (Arith.minus e₁ e₂).opt0Plus.eval s     := rfl
      -- | .mult e₁ e₂ => fun s =>
      --   have ih₁ := sound e₁ s
      --   have ih₂ := sound e₂ s
      --   calc (Arith.mult e₁ e₂).eval s
      --     _ = e₁.eval s * e₂.eval s                   := rfl
      --     _ = e₁.opt0Plus.eval s * e₂.opt0Plus.eval s := congr (congrArg Nat.mul ih₁) ih₂
      --     _ = (Arith.mult e₁ e₂).opt0Plus.eval s      := rfl

    theorem Logic.opt0Plus.sound: Logic.transform_sound Logic.opt0Plus
      | .true, _ => rfl
      | .false, _ => rfl
      | .eq e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        calc (Logic.eq e₁ e₂).eval s
          _ = BEq.beq (e₁.eval s) (e₂.eval s)                   := rfl
          _ = BEq.beq (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s) := congr (congrArg BEq.beq ih₁) ih₂
          _ = (Logic.eq e₁ e₂).opt0Plus.eval s                  := rfl
      | .neq e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        calc (Logic.neq e₁ e₂).eval s
          _ = not (BEq.beq (e₁.eval s) (e₂.eval s))                   := rfl
          _ = not (BEq.beq (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s)) := sorry --congr (congr (congrArg not BEq.beq ih₁) ih₂
          _ = (Logic.neq e₁ e₂).opt0Plus.eval s                       := rfl
      | .le e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        sorry
        -- calc (Logic.le e₁ e₂).eval s
        --   _ = (LE.le (e₁.eval s) (e₂.eval s): Bool)                   := rfl
        --   _ = (LE.le (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s): Bool) := congr (congrArg LE.le ih₁) ih₂
        --   _ = (Logic.le e₁ e₂).opt0Plus.eval s                        := rfl
      | .gt e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        sorry
        -- calc (Logic.gt e₁ e₂).eval s
        --   _ = (GT.gt (e₁.eval s) (e₂.eval s): Bool)                   := rfl
        --   _ = (GT.gt (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s): Bool) := congr (congrArg GT.gt ih₁) ih₂
        --   _ = (Logic.gt e₁ e₂).opt0Plus.eval s                        := rfl
      | .not b, s =>
        have ih := sound b s
        calc (Logic.not b).eval s
          _ = not (b.eval s)                := rfl
          _ = not (b.opt0Plus.eval s)       := congrArg not ih
          _ = (Logic.not b).opt0Plus.eval s := rfl
      | .and b₁ b₂, s =>
        have ih₁ := sound b₁ s
        have ih₂ := sound b₂ s
        calc (Logic.and b₁ b₂).eval s
          _ = and (b₁.eval s) (b₂.eval s)                   := rfl
          _ = and (b₁.opt0Plus.eval s) (b₂.opt0Plus.eval s) := congr (congrArg and ih₁) ih₂
          _ = (Logic.and b₁ b₂).opt0Plus.eval s              := rfl

    theorem Command.opt0Plus.sound: Command.transform_sound Command.opt0Plus := sorry
  end Term

  namespace Tactic
    theorem Arith.opt0Plus.sound: Arith.transform_sound Arith.opt0Plus := by
      intro e s
      induction e
      <;> try rfl
      case minus | mult =>
        unfold Arith.opt0Plus Arith.eval
        simp_all
      case plus e₁ e₂ ih₁ ih₂ =>
        cases e₁
        case num n =>
          cases n with
            | zero =>
              repeat rw [← ih₂]
              simp_all
            | succ n =>
              unfold Arith.opt0Plus
              simp_all
        case ident | plus | minus | mult =>
          unfold Arith.opt0Plus Arith.eval
          simp_all

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
      | .num _, _ => rfl
      | .ident _, _ => rfl
      | .plus (.num 0) e₂, s =>
        have ih₁ := sound (.num 0) s
        have ih₂ := sound e₂ s
        calc (Arith.plus (.num 0) e₂).eval s
          _ = (Arith.num 0).eval s + e₂.eval s                    := by rfl
          _ = (Arith.num 0).opt0Plus.eval s + e₂.opt0Plus.eval s  := by rw [ih₁, ih₂]
          _ = (Arith.plus (Arith.num 0) e₂).opt0Plus.eval s       := by simp
          _ = e₂.opt0Plus.eval s                                  := by rfl
      | .plus e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        calc (Arith.plus e₁ e₂).eval s
          _ = e₁.eval s + e₂.eval s                   := by rfl
          _ = e₁.opt0Plus.eval s + e₂.opt0Plus.eval s := by rw [ih₁, ih₂]
          _ = (Arith.plus e₁ e₂).opt0Plus.eval s      := by sorry --rfl
      | .minus e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        calc (Arith.minus e₁ e₂).eval s
          _ = e₁.eval s - e₂.eval s                   := by rfl
          _ = e₁.opt0Plus.eval s - e₂.opt0Plus.eval s := by rw [ih₁, ih₂]
          _ = (Arith.minus e₁ e₂).opt0Plus.eval s     := by rfl
      | .mult e₁ e₂, s =>
        have ih₁ := sound e₁ s
        have ih₂ := sound e₂ s
        calc (Arith.mult e₁ e₂).eval s
          _ = e₁.eval s * e₂.eval s                   := by rfl
          _ = e₁.opt0Plus.eval s * e₂.opt0Plus.eval s := by rw [ih₁, ih₂]
          _ = (Arith.mult e₁ e₂).opt0Plus.eval s      := by rfl

    theorem Logic.opt0Plus.sound: Logic.transform_sound Logic.opt0Plus
      | .true, _ => rfl
      | .false, _ => rfl
      | .eq e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        calc (Logic.eq e₁ e₂).eval s
          _ = BEq.beq (e₁.eval s) (e₂.eval s)                   := by rfl
          _ = BEq.beq (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s) := by rw [ih₁, ih₂]
          _ = (Logic.eq e₁ e₂).opt0Plus.eval s                  := by rfl
      | .neq e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        calc (Logic.neq e₁ e₂).eval s
          _ = not (BEq.beq (e₁.eval s) (e₂.eval s))                   := by rfl
          _ = not (BEq.beq (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s)) := by rw [ih₁, ih₂]
          _ = (Logic.neq e₁ e₂).opt0Plus.eval s                       := by rfl
      | .le e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        calc (Logic.le e₁ e₂).eval s
          _ = (LE.le (e₁.eval s) (e₂.eval s): Bool)                   := by rfl
          _ = (LE.le (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s): Bool) := by rw [ih₁, ih₂]
          _ = (Logic.le e₁ e₂).opt0Plus.eval s                        := by rfl
      | .gt e₁ e₂, s =>
        have ih₁ := Arith.opt0Plus.sound e₁ s
        have ih₂ := Arith.opt0Plus.sound e₂ s
        calc (Logic.gt e₁ e₂).eval s
          _ = (GT.gt (e₁.eval s) (e₂.eval s): Bool)                   := by rfl
          _ = (GT.gt (e₁.opt0Plus.eval s) (e₂.opt0Plus.eval s): Bool) := by rw [ih₁, ih₂]
          _ = (Logic.gt e₁ e₂).opt0Plus.eval s                        := by rfl
      | .not b, s =>
        have ih := sound b s
        calc (Logic.not b).eval s
          _ = not (b.eval s)                := by rfl
          _ = not (b.opt0Plus.eval s)       := by rw [ih]
          _ = (Logic.not b).opt0Plus.eval s := by rfl
      | .and b₁ b₂, s =>
        have ih₁ := sound b₁ s
        have ih₂ := sound b₂ s
        calc (Logic.and b₁ b₂).eval s
          _ = and (b₁.eval s) (b₂.eval s)                   := by rfl
          _ = and (b₁.opt0Plus.eval s) (b₂.opt0Plus.eval s) := by rw [ih₁, ih₂]
          _ = (Logic.and b₁ b₂).opt0Plus.eval s             := by rfl

    theorem Command.opt0Plus.sound: Command.transform_sound Command.opt0Plus := sorry
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
  def _root_.Arith.subst (within: Arith) (var: String) (repl: Arith): Arith :=
    match within with
      | .num n => .num n
      | .ident id => if id == var then repl else .ident id
      | .plus e₁ e₂ => .plus (subst e₁ var repl) (subst e₂ var repl)
      | .minus e₁ e₂ => .minus (subst e₁ var repl) (subst e₂ var repl)
      | .mult e₁ e₂ => .mult (subst e₁ var repl) (subst e₂ var repl)

  example: (("Y": Arith) + "X").subst "X" (42 + 53) = "Y" + (42 + 53) := rfl

  def Arith.subst.equiv: Prop := ∀ id₁ id₂ e₁ e₂, (Command.seq (.assign id₁ e₁) (.assign id₂ e₂)).equiv (.seq (.assign id₁ e₁) (.assign id₂ (e₂.subst id₁ e₁)))

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

    def Command.equiv (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, CommandEval c₁ s₁ s₂ ↔ CommandEval c₂ s₁ s₂

    private def xy: Command := .seq (.havoc "X") (.havoc "Y")
    private def yx: Command := .seq (.havoc "Y") (.havoc "X")
    private def copy: Command := .seq (.havoc "X") (.assign "Y" "X")
    private def whileHavoc: Command :=
      .while (.not (.eq "X" 0))
        (.seq (.havoc "X") (.assign "X" ("X" + 1)))
    private def whileSkip: Command := .while (.not (.eq "X" 0)) .skip
    private def havocHavoc: Command :=
      .while (.neq "X" 0)
        (.seq (.havoc "X") (.havoc "Y"))
    private def noHavoc: Command := .seq (.assign "X" 0) (.assign "Z" 1)

    namespace Term
      example: CommandEval (.havoc "X") State.empty (State.build [("X", 0)]) := sorry
      example: CommandEval (.seq .skip (.havoc "Z")) State.empty (State.build [("Z", 42)]) := sorry

      example: xy.equiv yx ∨ ¬(xy.equiv yx) := sorry
      example: xy.equiv copy ∨ ¬(xy.equiv copy) := sorry

      example: whileHavoc.equiv whileSkip :=
        sorry
        where
          havoc_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(CommandEval whileHavoc s₁ s₂) := sorry
          skip_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(CommandEval whileSkip s₁ s₂) := sorry

      example: ¬(havocHavoc.equiv noHavoc) := sorry

      example: (Command.while (.neq "X" 1) (.havoc "X")).equiv (.assign "X" 1) := sorry
    end Term

    namespace Tactic
      example: CommandEval (.havoc "X") State.empty (State.build [("X", 0)]) := by sorry
      example: CommandEval (.seq .skip (.havoc "Z")) State.empty (State.build [("Z", 42)]) := by sorry

      example: xy.equiv yx ∨ ¬(xy.equiv yx) := by sorry
      example: xy.equiv copy ∨ ¬(xy.equiv copy) := by sorry

      example: whileHavoc.equiv whileSkip := by
        sorry
        where
          havoc_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(CommandEval whileHavoc s₁ s₂) := by sorry
          skip_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(CommandEval whileSkip s₁ s₂) := by sorry

      example: ¬(havocHavoc.equiv noHavoc) := by sorry

      example: (Command.while (.neq "X" 1) (.havoc "X")).equiv (.assign "X" 1) := by sorry
    end Tactic

    namespace Blended
      example: CommandEval (.havoc "X") State.empty (State.build [("X", 0)]) := sorry
      example: CommandEval (.seq .skip (.havoc "Z")) State.empty (State.build [("Z", 42)]) := sorry

      example: xy.equiv yx ∨ ¬(xy.equiv yx) := sorry
      example: xy.equiv copy ∨ ¬(xy.equiv copy) := sorry

      example: whileHavoc.equiv whileSkip :=
        sorry
        where
          havoc_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(CommandEval whileHavoc s₁ s₂) := sorry
          skip_may_diverge (s₁ s₂: State) (h: s₁ "X" ≠ 0): ¬(CommandEval whileSkip s₁ s₂) := sorry

      example: ¬(havocHavoc.equiv noHavoc) := sorry

      example: (Command.while (.neq "X" 1) (.havoc "X")).equiv (.assign "X" 1) := sorry
    end Blended
  end Havoc

  /-
  ## Additional Exercises
  -/

  -- How is this different from "refines" above?
  @[reducible] def _root_.Command.approx  (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, CommandEval c₁ s₁ s₂ → CommandEval c₂ s₁ s₂

  private def approx_c₁: Command := .while (.neq "X" 1) (.assign "X" ("X" - 1))
  private def approx_c₂: Command := .assign "X" 1

  private def approx_c₃: Command := sorry
  private def approx_c₄: Command := sorry

  private def approx_min: Command := sorry

  private def _root_.Command.zProp (c: Command): Prop := sorry

  namespace Term
    example (id₁ id₂: String) (e₁ e₂: Arith) (h₁: OccursCheck id₁ e₁) (h₂: OccursCheck id₂ e₂): (Command.seq (.assign id₁ e₁) (.assign id₂ e₂)).equiv (.seq (.assign id₂ e₂) (.assign id₁ e₁)) := sorry

    -- TODO: For loops in Imp

    example: ¬(approx_c₃.approx approx_c₄) ∧ ¬(approx_c₄.approx approx_c₃) := sorry
    example (c: Command): approx_min.approx c := sorry
    example (c₁ c₂: Command) (h₁: c₁.zProp) (h₂: c₁.approx c₂): c₂.zProp := sorry
  end Term

  namespace Tactic
    example (id₁ id₂: String) (e₁ e₂: Arith) (h₁: OccursCheck id₁ e₁) (h₂: OccursCheck id₂ e₂): (Command.seq (.assign id₁ e₁) (.assign id₂ e₂)).equiv (.seq (.assign id₂ e₂) (.assign id₁ e₁)) := by sorry

    -- TODO: For loops in Imp

    example: ¬(approx_c₃.approx approx_c₄) ∧ ¬(approx_c₄.approx approx_c₃) := by sorry
    example (c: Command): approx_min.approx c := by sorry
    example (c₁ c₂: Command) (h₁: c₁.zProp) (h₂: c₁.approx c₂): c₂.zProp := by sorry
  end Tactic

  namespace Blended
    example (id₁ id₂: String) (e₁ e₂: Arith) (h₁: OccursCheck id₁ e₁) (h₂: OccursCheck id₂ e₂): (Command.seq (.assign id₁ e₁) (.assign id₂ e₂)).equiv (.seq (.assign id₂ e₂) (.assign id₁ e₁)) := sorry

    -- TODO: For loops in Imp

    example: ¬(approx_c₃.approx approx_c₄) ∧ ¬(approx_c₄.approx approx_c₃) := sorry
    example (c: Command): approx_min.approx c := sorry
    example (c₁ c₂: Command) (h₁: c₁.zProp) (h₂: c₁.approx c₂): c₂.zProp := sorry
  end Blended
end SoftwareFoundations.ProgrammingLanguageFoundations.Equiv
