/-
# Program Equivalence
-/

import Mathlib.tactic.linarith

import «SoftwareFoundations».«LogicalFoundations».«Maps»
import «SoftwareFoundations».«LogicalFoundations».«Imp»

/-
## Behavioral Equivalence
-/

/-
### Definitions
-/

def Arith.equiv (a₁ a₂: Arith): Prop := ∀ s: State, a₁.eval s = a₂.eval s
def Logic.equiv (l₁ l₂: Logic): Prop := ∀ s: State, l₁.eval s = l₂.eval s

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

def Command.equiv (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, CommandEval c₁ s₁ s₂ ↔ CommandEval c₂ s₁ s₂
def Command.refines (c₁ c₂: Command): Prop := ∀ s₁ s₂: State, CommandEval c₁ s₁ s₂ → CommandEval c₂ s₁ s₂

/-
### Simple Examples
-/

example (c: Command): (Command.seq .skip c).equiv c :=
  fun s₁ s₂ =>
    have mp: CommandEval (Command.seq .skip c) s₁ s₂ → CommandEval c s₁ s₂
      | .seq .skip c _ _ s₃ (.skip s) h₂ => h₂
    have mpr: CommandEval c s₁ s₂ → CommandEval (Command.seq .skip c) s₁ s₂
      | .skip _                        => .seq _ _ _ _ _ (.skip _) (.skip _)
      | .assign _ _ _ _ h              => .seq _ _ _ _ _ (.skip _) (.assign _ _ _ _ h)
      | .seq _ _ _ s₂ _ h₁ h₂          => .seq _ _ _ _ _ (.skip _) (.seq _ _ _ s₂ _ h₁ h₂)
      | .ifTrue _ _ _ _ _ h₁ h₂        => .seq _ _ _ _ _ (.skip _) (.ifTrue _ _ _ _ _ h₁ h₂)
      | .ifFalse _ _ _ _ _ h₁ h₂       => .seq _ _ _ _ _ (.skip _) (.ifFalse _ _ _ _ _ h₁ h₂)
      | .whileTrue _ s₂ _ _ _ h₁ h₂ h₃ => .seq _ _ _ _ _ (.skip _) (.whileTrue _ s₂ _ _ _ h₁ h₂ h₃)
      | .whileFalse _ _ _ h₁           => .seq _ _ _ _ _ (.skip _) (.whileFalse _ _ _ h₁)
    ⟨mp, mpr⟩

theorem Command.skip_left (c: Command): (Command.seq .skip c).equiv c := by
  unfold Command.equiv
  intro s₁ s₂
  apply Iff.intro
  · intro h
    cases h with
      | seq c₁ c₂ s₁ s₂ s₃ h₁ h₂ =>
        cases h₁ with
          | skip => exact h₂
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


example (c: Command): (Command.seq c .skip).equiv c :=
  fun s₁ s₂ =>
    have mp: CommandEval (Command.seq c .skip) s₁ s₂ → CommandEval c s₁ s₂
      | .seq c .skip s₁ s _ h₁ (.skip _) => h₁
    have mpr: CommandEval c s₁ s₂ → CommandEval (Command.seq c .skip) s₁ s₂
      | .skip _                        => .seq _ _ _ _ _ (.skip _) (.skip _)
      | .assign _ _ _ _ h              => .seq _ _ _ _ _ (.assign _ _ _ _ h) (.skip _)
      | .seq _ _ _ s₂ _ h₁ h₂          => .seq _ _ _ _ _ (.seq _ _ _ s₂ _ h₁ h₂) (.skip _)
      | .ifTrue _ _ _ _ _ h₁ h₂        => .seq _ _ _ _ _ (.ifTrue _ _ _ _ _ h₁ h₂) (.skip _)
      | .ifFalse _ _ _ _ _ h₁ h₂       => .seq _ _ _ _ _ (.ifFalse _ _ _ _ _ h₁ h₂) (.skip _)
      | .whileTrue _ s₂ _ _ _ h₁ h₂ h₃ => .seq _ _ _ _ _ (.whileTrue _ s₂ _ _ _ h₁ h₂ h₃) (.skip _)
      | .whileFalse _ _ _ h₁           => .seq _ _ _ _ _ (.whileFalse _ _ _ h₁) (.skip _)
    ⟨mp, mpr⟩

theorem Command.skip_right (c: Command): (Command.seq c .skip).equiv c := by
  unfold Command.equiv
  intro s₁ s₂
  apply Iff.intro
  · intro h
    cases h with
      | seq c₁ c₂ s₁ s₂ s₃ h₁ h₂ =>
        cases h₂ with
          | skip => exact h₁
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

example (t f: Command): (Command.if .true t f).equiv t :=
  fun s₁ s₂ =>
    have mp: CommandEval (.if .true t f) s₁ s₂ → CommandEval t s₁ s₂
      | .ifTrue _ _ _ _ _ _ h₂ => h₂
      | .ifFalse _ _ _ _ _ _ _ => by contradiction -- TODO: Remove the tactic block
    have mpr: CommandEval t s₁ s₂ → CommandEval (.if .true t f) s₁ s₂
      | .skip _                        => .ifTrue _ _ _ _ _ rfl (.skip _)
      | .assign _ _ _ _ h              => .ifTrue _ _ _ _ _ rfl (.assign _ _ _ _ h)
      | .seq _ _ _ s _ h₁ h₂           => .ifTrue _ _ _ _ _ rfl (.seq _ _ _ s _ h₁ h₂)
      | .ifTrue _ _ _ _ _ h₁ h₂        => .ifTrue _ _ _ _ _ rfl (.ifTrue _ _ _ _ _ h₁ h₂)
      | .ifFalse _ _ _ _ _ h₁ h₂       => .ifTrue _ _ _ _ _ rfl (.ifFalse _ _ _ _ _ h₁ h₂)
      | .whileTrue _ s₂ _ _ _ h₁ h₂ h₃ => .ifTrue _ _ _ _ _ rfl (.whileTrue _ s₂ _ _ _ h₁ h₂ h₃)
      | .whileFalse _ _ _ h            => .ifTrue _ _ _ _ _ rfl (.whileFalse _ _ _ h)
    ⟨mp, mpr⟩

theorem Command.if_true_simple (t f: Command): (Command.if .true t f).equiv t := by
  unfold Command.equiv
  intro s₁ s₂
  apply Iff.intro
  · intro h
    cases h with
      | ifTrue _ _ _ _ _ _ h₂ => exact h₂
      | ifFalse => contradiction
  · intro h
    cases h
    <;> try (apply CommandEval.ifTrue
             · unfold Logic.eval
               rfl
             · constructor
               repeat assumption)

    case ifFalse c t f h₁ h₂ =>
      apply CommandEval.ifTrue
      · unfold Logic.eval
        rfl
      . constructor
        · sorry
        · sorry
    case whileFalse c b h₁ =>
      apply CommandEval.ifTrue
      · unfold Logic.eval
        rfl
      . constructor
        · sorry
        · sorry
        · sorry
        · sorry

example (b: Logic) (c₁ c₂: Command) (h₁: b.equiv .true): (Command.if b c₁ c₂).equiv c₁ := by sorry
theorem Command.if_true (b: Logic) (c₁ c₂: Command) (h₁: b.equiv .true): (Command.if b c₁ c₂).equiv c₁ := by sorry

example (b: Logic) (c₁ c₂: Command) (h₁: b.equiv .false): (Command.if b c₁ c₂).equiv c₂ := by sorry
theorem Command.if_false (b: Logic) (c₁ c₂: Command) (h₁: b.equiv .false): (Command.if b c₁ c₂).equiv c₂ := by sorry

example (b: Logic) (c₁ c₂: Command): (Command.if b c₁ c₂).equiv (Command.if (.not b) c₂ c₁) := sorry
theorem Command.if_swap (b: Logic) (c₁ c₂: Command): (Command.if b c₁ c₂).equiv (Command.if (.not b) c₂ c₁) := by sorry

example (c: Logic) (b: Command) (h₁: c.equiv .false): (Command.while c b).equiv Command.skip :=
  sorry
  where
    while_false_nonterm: Nat := sorry
theorem Command.while_false (c: Logic) (b: Command) (h₁: c.equiv .false): (Command.while c b).equiv Command.skip := by
  sorry
  where
    while_false_nonterm: Nat := sorry

example (c: Logic) (b: Command) (h₁: c.equiv .true): (Command.while c b).equiv (Command.while .true Command.skip) :=
  sorry
  where
    while_true_nonterm: Nat := sorry
theorem Command.while_true (c: Logic) (b: Command) (h₁: c.equiv .true): (Command.while c b).equiv (Command.while .true Command.skip) := by
  sorry
  where
    while_true_nonterm: Nat := sorry

example (c: Logic) (b: Command): (Command.while c b).equiv (Command.if c (Command.seq b (Command.while c b)) .skip) := sorry
theorem Command.loop_unrolling (c: Logic) (b: Command): (Command.while c b).equiv (Command.if c (Command.seq b (Command.while c b)) .skip) := by sorry

example (c₁ c₂ c₂: Command): (Command.seq (Command.seq c₁ c₂) c₃).equiv (Command.seq c₁ (Command.seq c₂ c₃)) := sorry
theorem Command.seq_assoc (c₁ c₂ c₂: Command): (Command.seq (Command.seq c₁ c₂) c₃).equiv (Command.seq c₁ (Command.seq c₂ c₃)) := by sorry

example (id: String): (Command.assign "X" "X").equiv Command.skip := sorry
theorem Command.identity_assignment (id: String): (Command.assign "X" "X").equiv Command.skip := by sorry

example (id: String) (e: Arith) (h₁: (id: Arith).equiv e): Command.skip.equiv (Command.assign id e) := sorry
theorem Command.assign_arith_equiv (id: String) (e: Arith) (h₁: (id: Arith).equiv e): Command.skip.equiv (Command.assign id e) := by sorry

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
