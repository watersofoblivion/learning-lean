/-
# Hoare Logic as a Logic
-/

import SoftwareFoundations.LogicalFoundations.Maps
import SoftwareFoundations.LogicalFoundations.Imp
import SoftwareFoundations.ProgrammingLanguageFoundations.Hoare

namespace SoftwareFoundations.ProgrammingLanguageFoundations.Hoare
  open SoftwareFoundations.LogicalFoundations.Maps
  open SoftwareFoundations.LogicalFoundations.Imp

  /-
  ## Hoare Logic and Model Theory
  -/

  /-
  ## Hoare Logic and Proof Theory
  -/

  /-
  ## Derivability
  -/

  inductive HoareLogic: Assertion → Command → Assertion → Type :=
    | skip {P: Assertion}: HoareLogic P .skip P
    | assign {Q: Assertion} {id: String} {e: Arith}: HoareLogic [Assert| ‹Q› [ ‹id› ↦ ‹e› ]] [Imp| ‹id› := ‹e› ] Q
    | seq {P Q R: Assertion} {c₁ c₂: Command} (h₁: HoareLogic Q c₂ R) (h₂: HoareLogic P c₁ Q): HoareLogic P [Imp| ‹c₁›; ‹c₂› ] R
    | if {P Q: Assertion} {c: Logic} {t f: Command} (h₁: HoareLogic _ t Q) (h₂: HoareLogic _ f Q): HoareLogic P [Imp| ite (‹c›) { ‹t› } else { ‹f› }] Q
    | while {P: Assertion} {c: Logic} {b: Command} (h₁: HoareLogic _ b P): HoareLogic P [Imp| while (‹c›) { ‹b› }] _
    | consequence {P₁ P₂ Q₁ Q₂: Assertion} {c: Command} (h₁: HoareLogic P₂ c Q₂) (h₂: (s: State) → P₁ s → P₂ s) (h₃: (s: State) → Q₂ s → Q₁ s): HoareLogic P₁ c Q₁

  namespace Term
    example (P₁ P₂ Q: Assertion) (c: Command) (h₁: HoareLogic P₂ c Q) (h₂: (s: State) → P₁ s → P₂ s): HoareLogic P₁ c Q := sorry
    example (P Q₁ Q₂: Assertion) (c: Command) (h₁: HoareLogic P c Q₂) (h₂: (s: State) → Q₂ s → Q₁ s): HoareLogic P c Q₁ := sorry

    example: [Hoare| ⦃(X = 3) [X ↦ X + 2] [X ↦ X + 1]⦄ X := X + 1; X := X + 2 ⦃(X = 3)⦄] := sorry

    theorem HoareLogic.true_post {P: Assertion} {c: Command}: HoareLogic P c True := sorry
    theorem HoareLogic.false_pre {Q: Assertion} {c: Command}: HoareLogic False c Q := sorry
  end Term

  /-
  ## Soundness and Completeness
  -/

  def _root_.SoftwareFoundations.ProgrammingLanguageFoundations.Hoare.Assertion.weakestPrecondition (Q: Assertion) (c: Command)
    | s₁, s₂ => (s₁ =[c]=> s₂) → Q s₂

  namespace Term
    theorem HoareLogic.sound {P Q: Assertion} {c: Command} (h: HoareLogic P c Q): HoareTriple P c Q := sorry

    theorem Assertion.weakestPrecondition.is_precondition {Q: Assertion} {c: Command}: [Hoare| ⦃ ‹Q.weakestPrecondition c› ⦄ ‹c› ⦃ ‹Q› ⦄] := sorry
    theorem Assertion.weakestPrecondition.is_weakest {P Q: Assertion} {c: Command} (h: [Hoare| ⦃ ‹P› ⦄ ‹c› ⦃ ‹Q› ⦄]): [Assert| ‹P› → ‹Q.weakestPrecondition c›] := sorry

    theorem Assertion.weakestPrecondition.seq {P Q: Assertion} {c₁ c₂: Command} (h₁: HoareLogic P c₁ (Q.weakestPrecondition c₂)) (h₂: HoareLogic (Q.weakestPrecondition c₂) c₂ Q): HoareLogic P [Imp| ‹c₁›; ‹c₂›] Q := sorry
    theorem Assertion.weakestPrecondition.invariant {Q: Assertion} {c: Logic} {b: Command}: [Hoare| ...] := sorry

    theorem HoareLogic.complete {P Q: Assertion} {c: Command} (h: [Hoare| ⦃ ‹P› ⦄ ‹c› ⦃ ‹Q› ⦄]): HoareLogic P c Q := sorry
  end Term

  /-
  ## Postscript: Decidability
  -/
end SoftwareFoundations.ProgrammingLanguageFoundations.Hoare
