/-
# Hoare Logic, Part 1
-/

import «SoftwareFoundations».«LogicalFoundations».«Imp»
import «SoftwareFoundations».«LogicalFoundations».«Maps»

namespace SoftwareFoundations.ProgrammingLanguageFoundations.Hoare
  open SoftwareFoundations.LogicalFoundations.Imp

  /-
  ## Assertions
  -/

  def Assertion: Type := State → Prop

  section
    private def assertionOne: Assertion
      | s => s "X" ≤ s "Y"
    private def assertionTwo: Assertion
      | s => s "X" = 3 ∨ s "X" ≤ s "Y"
    private def assertionThree: Assertion
      | s => s "Z" * s "Z" ≤ s "X" ∧ ¬((s "Z").succ * (s "Z").succ ≤ s "X")
    private def assertionFour: Assertion
      | s => s "Z" = max (s "X") (s "Y")
  end

  @[reducible]
  def Assertion.implies (P Q: Assertion): Assertion := fun s => P s → Q s
  def Assertion.iff (P Q: Assertion): Assertion := fun s => implies P Q s ∧ implies Q P s
  def Assertion.and (P Q: Assertion): Assertion := fun s => P s ∧ Q s
  def Assertion.or (P Q: Assertion): Assertion := fun s => P s ∨ Q s
  def Assertion.not (P: Assertion): Assertion := fun s => ¬ P s
  def Assertion.eq (P Q: Assertion): Assertion := fun s => P s = Q s
  def Assertion.neq (P Q: Assertion): Assertion := fun s => P s ≠ Q s
  def Assertion.lt (P Q: Assertion): Assertion := fun s => P s < Q s
  def Assertion.le (P Q: Assertion): Assertion := fun s => P s ≤ Q s
  def Assertion.gt (P Q: Assertion): Assertion := fun s => P s > Q s
  def Assertion.ge (P Q: Assertion): Assertion := fun s => P s ≥ Q s
  -- def Assertion.add (P Q: Assertion): Assertion := fun s => P s + Q s

  /-
  ## Hoare Triples, Informally
  -/

  /-
  ## Hoare Triples, Formally
  -/

  @[reducible]
  def HoareTriple (P: Assertion) (c: Command) (Q: Assertion): Prop :=
    ∀ s₁ s₂: State, P s₁ → CommandEval c s₁ s₂ → Q s₂

  theorem HoareTriple.post_true {P Q: Assertion} {c: Command}: (h: (s: State) → Q s) → HoareTriple P c Q
    | h, s₁, s₂, hp, c => sorry

  theorem HoareTriple.pre_false {P Q: Assertion} {c: Command}: (h: (s: State) → ¬P s) → HoareTriple P c Q
    | h, s₁, s₂, hp, c => sorry

  /-
  ## Proof Rules
  -/

  /-
  ### Skip
  -/

  def HoareTriple.skip {P: Assertion}: HoareTriple P .skip P
    | _, _, hp, .skip _ => hp

  /-
  ### Sequencing
  -/

  def HoareTriple.seq {P Q R: Assertion} {c₁ c₂: Command} (h₁: HoareTriple Q c₂ R) (h₂: HoareTriple P c₁ Q): HoareTriple P (.seq c₁ c₂) R
    | _, _, hp, .seq _ _ _ h₃ h₄ =>
      have hq := h₂ _ _ hp h₃
      h₁ _ _ hq h₄

  /-
  ### Assignment
  -/

  @[reducible]
  def Assertion.subst (id: String) (e: Arith) (P: Assertion): Assertion
    | s => P (s.update id (e.eval s))

  def HoareTriple.assign {Q: Assertion} {id: String} {e: Arith}: HoareTriple (Q.subst id e) (.assign id e) Q
    | _,_, hqs, .assign _ h =>
      -- TODO: Remove Tactic Block
      by
        unfold Assertion.subst at hqs
        simp at hqs
        rw [h] at hqs
        exact hqs

  -- TODO: Complete assertions and implement example(s)

  /-
  ### Consequence
  -/

  /-
  ### Automation
  -/

  /-
  ### Sequencing + Assignment
  -/

  /-
  ### Conditionals
  -/

  /-
  #### Example
  -/

  /-
  #### Exercise: One-Sided Conditionals
  -/

  /-
  ### While Loops
  -/

  /-
  #### Exercise: Repeat
  -/

  /-
  ## Summary
  -/

  /-
  ## Additional Examples
  -/

  /-
  ### Havoc
  -/

  /-
  ### Assert and Assume
  -/
end SoftwareFoundations.ProgrammingLanguageFoundations.Hoare
