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
  def NatAssertion: Type := State → Nat

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

  declare_syntax_cat nat_assert

  syntax num : nat_assert
  syntax ident : nat_assert
  syntax:60 nat_assert:60 "+" nat_assert:61 : nat_assert
  syntax:60 nat_assert:60 "-" nat_assert:61 : nat_assert
  syntax:70 nat_assert:70 "*" nat_assert:71 : nat_assert
  syntax:30 "app₁" "‹" term "›" nat_assert : nat_assert
  syntax:30 "app₂" "‹" term "›" nat_assert nat_assert : nat_assert
  syntax "(" nat_assert ")" : nat_assert

  syntax "[NatAssert|" nat_assert "]" : term

  macro_rules
    | `([NatAssert| $n:num])                                     => `(((fun _ => $n): NatAssertion))
    | `([NatAssert| $id:ident])                                  => `(((fun s => s $(Lean.quote (toString id.getId))): NatAssertion))
    | `([NatAssert| $x + $y])                                    => `(((fun s => ([NatAssert| $x] s) + ([NatAssert| $y] s)): NatAssertion))
    | `([NatAssert| $x - $y])                                    => `(((fun s => ([NatAssert| $x] s) - ([NatAssert| $y] s)): NatAssertion))
    | `([NatAssert| $x * $y])                                    => `(((fun s => ([NatAssert| $x] s) * ([NatAssert| $y] s)): NatAssertion))
    | `([NatAssert| app₂ ‹$f:term› $x:nat_assert $y:nat_assert]) => `(((fun s => $(Lean.quote f) ([NatAssert| $x] s) ([NatAssert| $y] s)): NatAssertion))
    | `([NatAssert| app₁ ‹$f:term› $x:nat_assert])               => `(((fun s => $(Lean.quote f) ([NatAssert| $x] s)): NatAssertion))
    | `([NatAssert| ( $a:nat_assert )])                          => `([NatAssert| $a])

  section
    example: [NatAssert| 42] [State|] = 42 := rfl
    example: [NatAssert| 1 + 2] [State|] = 3 := rfl
    example: [NatAssert| 2 - 1] [State|] = 1 := rfl
    example: [NatAssert| 2 * 4] [State|] = 8 := rfl

    example: [NatAssert| (2 + 58) * (4 - 4)] [State|] = 0 := rfl

    example: [NatAssert| X] [State| X = 42] = 42 := rfl
    example: [NatAssert| X + Y] [State| X = 1, Y = 2] = 3 := rfl

    example: [NatAssert| (app₁ ‹Nat.succ› 1)] [State|] = 2 := rfl
    example: [NatAssert| app₁ ‹Nat.succ› 1] [State|] = 2 := rfl
    example: [NatAssert| (app₁ ‹Nat.succ› X)] [State| X = 1] = 2 := rfl
    example: [NatAssert| app₁ ‹Nat.succ› X] [State| X = 1] = 2 := rfl
    example: [NatAssert| (app₂ ‹max› 1 2)] [State|] = 2 := rfl
    example: [NatAssert| app₂ ‹max› X Y] [State| X = 1, Y = 2] = 2 := rfl
  end

  declare_syntax_cat assert

  syntax nat_assert : assert
  syntax:min assert "→" assert : assert
  syntax:min assert "↔" assert : assert
  syntax:35 assert:36 "∧" assert:30 : assert
  syntax:30 assert:31 "∨" assert:30 : assert
  syntax:max "¬" assert:40 : assert
  syntax:50 nat_assert "=" nat_assert : assert
  syntax:50 nat_assert "≠" nat_assert : assert
  syntax:50 nat_assert "<" nat_assert : assert
  syntax:50 nat_assert "≤" nat_assert : assert
  syntax:50 nat_assert ">" nat_assert : assert
  syntax:50 nat_assert "≥" nat_assert : assert
  syntax "(" assert ")" : assert
  syntax "‹prop:" term "›" : assert
  syntax "‹" term "›" : assert

  syntax "[Assert|" assert "]" : term

  macro_rules
    | `([Assert| ‹prop: $P:term › ])             => `(((fun _ => $(Lean.quote P)): Assertion))
    | `([Assert| ‹$P:term› ])                    => `($(Lean.quote P))
    | `([Assert| $P → $Q])                       => `(((fun s => [Assert| $P] s → [Assert| $Q] s): Assertion))
    | `([Assert| $P ↔ $Q])                       => `(((fun s => [Assert| $P] s ↔ [Assert| $Q] s): Assertion))
    | `([Assert| $P ∧ $Q])                       => `(((fun s => [Assert| $P] s ∧ [Assert| $Q] s): Assertion))
    | `([Assert| $P ∨ $Q])                       => `(((fun s => [Assert| $P] s ∨ [Assert| $Q] s): Assertion))
    | `([Assert| ¬ $P])                          => `(((fun s => ¬ [Assert| $P] s): Assertion))
    | `([Assert| $P:nat_assert = $Q:nat_assert]) => `(((fun s => [NatAssert| $P] s = [NatAssert| $Q] s): Assertion))
    | `([Assert| $P:nat_assert ≠ $Q:nat_assert]) => `(((fun s => [NatAssert| $P] s ≠ [NatAssert| $Q] s): Assertion))
    | `([Assert| $P:nat_assert ≤ $Q:nat_assert]) => `(((fun s => [NatAssert| $P] s ≤ [NatAssert| $Q] s): Assertion))
    | `([Assert| $P:nat_assert < $Q:nat_assert]) => `(((fun s => [NatAssert| $P] s < [NatAssert| $Q] s): Assertion))
    | `([Assert| $P:nat_assert ≥ $Q:nat_assert]) => `(((fun s => [NatAssert| $P] s ≥ [NatAssert| $Q] s): Assertion))
    | `([Assert| $P:nat_assert > $Q:nat_assert]) => `(((fun s => [NatAssert| $P] s > [NatAssert| $Q] s): Assertion))
    | `([Assert| ( $a:assert )])                 => `([Assert| $a])

  section
    private def ex₁ := [Assert| X = 3]
    private def ex₂ := [Assert| ‹prop: True ›]
    private def ex₃ := [Assert| ‹prop: False ›]

    private def ex₄ := [Assert| X ≤ Y]
    private def ex₅ := [Assert| X = 3 ∨ X < Y]
    private def ex₆ := [Assert| X = 3 ∧ X < Y]
    private def ex₇ := [Assert| X = (app₂ ‹max› X Y)]
    private def ex₈ := [Assert| Z * Z ≤ X + 99]
    private def ex₉ := [Assert| Z * Z ≤ X ∨ ¬((app₁ ‹Nat.succ› Z) * (app₁ ‹Nat.succ› Z) ≤ X)]

    private def ex₁₀ := [Assert| ¬ X + 42 ≥ 99 - Q]
    private def ex₁₁ := [Assert| X + 42 ≥ 99 - Q → J = 4 ∧ P ≤ 5]
    private def ex₁₂ := [Assert| X + 42 ≥ 99 - Q ↔ J = 4 ∧ P ≤ 5]

    private def ex₁₃ (P: Assertion) := [Assert| ‹P› ]
  end

  /-
  ## Hoare Triples, Informally
  -/

  /-
  ## Hoare Triples, Formally
  -/

  @[reducible]
  def HoareTriple (P: Assertion) (c: Command) (Q: Assertion): Prop :=
    ∀ s₁ s₂: State, P s₁ → CommandEval c s₁ s₂ → Q s₂

  declare_syntax_cat hoare

  syntax "⦃" assert "⦄" cmd "⦃" assert "⦄" : hoare

  syntax "[Hoare|" hoare "]" : term

  macro_rules
    | `([Hoare| ⦃ $pre:assert ⦄ $c:cmd ⦃ $post:assert ⦄ ]) => `(HoareTriple [Assert| $pre] [Imp| $c] [Assert| $post])

  theorem HoareTriple.post_true {P Q: Assertion} {c: Command}: (h: (s: State) → Q s) → [Hoare| ⦃ ‹P› ⦄ ‹c› ⦃ ‹Q› ⦄]
    | h, s₁, s₂, hp, c =>
      [Hoare| ⦃ ‹prop:h s₁› ⦄ ‹c› ⦃ ‹hp› ⦄]

  theorem HoareTriple.pre_false {P Q: Assertion} {c: Command}: (h: (s: State) → ¬P s) → [Hoare| ⦃ ‹P› ⦄ ‹c› ⦃ ‹Q› ⦄]
    | h, s₁, s₂, hp, c => sorry

  /-
  ## Proof Rules
  -/

  /-
  ### Skip
  -/

  def HoareTriple.skip {P: Assertion}: [Hoare| ⦃ ‹P› ⦄ skip ⦃ ‹P› ⦄]
    | _, _, hp, .skip _ => hp

  /-
  ### Sequencing
  -/

  def HoareTriple.seq {P Q R: Assertion} {c₁ c₂: Command} (h₁: [Hoare| ⦃ ‹Q› ⦄ ‹c₂› ⦃ ‹R› ⦄]) (h₂: [Hoare| ⦃ ‹P› ⦄ ‹c₁› ⦃ ‹Q› ⦄]): [Hoare| ⦃ ‹P› ⦄ ‹c₁›; ‹c₂› ⦃ ‹R› ⦄]
    | _, _, hp, .seq _ _ _ h₃ h₄ =>
      have hq := h₂ _ _ hp h₃
      h₁ _ _ hq h₄

  /-
  ### Assignment
  -/

  @[reducible]
  def Assertion.subst (id: String) (e: Arith) (P: Assertion): Assertion
    | s => P (s.update id (e.eval s))

  notation P "[" id "↦" e "]" => Assertion.subst id e P

  def HoareTriple.assign {Q: Assertion} {id: String} {e: Arith}: [Hoare| ⦃Q [id ↦ e]⦄ ‹id› := ‹e›) ⦃Q⦄]
    | _,_, hqs, .assign _ h =>
      have h :=
        calc Assertion.subst id e Q _
          _ = Q (LogicalFoundations.Maps.TotalMap.update _ id (Arith.eval _ e)) := rfl
          _ = Q (LogicalFoundations.Maps.TotalMap.update _ id _)                := congrArg Q (congrArg (LogicalFoundations.Maps.TotalMap.update _ id) h)
      -- TODO: Remove Tactic Block
      by rw [h] at hqs; exact hqs

  namespace Term
    example: [Hoare| ⦃(X < 5) [X ↦ X + 1]⦄ X := X + 1 ⦃X < 5⦄] :=
      HoareTriple.assign

    example: ∃ P, [Hoare| ⦃ ‹P› ⦄ X := 2 * X ⦃X ≤ 10⦄] :=
      ⟨[Assert| X ≤ 5], sorry⟩

    example: ∃ P, [Hoare| ⦃ ‹P› ⦄ X := 3 ⦃(X ≤ 0 ∧ X ≤ 5)⦄] :=
      ⟨[Assert| ‹prop:True› ], sorry⟩

    example: ∃ E: Arith, ¬ [Hoare| ⦃ ‹prop: True› ⦄ X := ‹e› ⦃X = e⦄] := sorry
    example (n: Nat) (e: Arith) (P: Assertion): [Hoare| ⦃ ‹fun s => P s ∧ s "X" = n› ⦄ X := ‹e› ⦃ ‹fun s => P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)› ⦄] := sorry
    example (e: Arith) (P: Assertion): [Hoare| ⦃ ‹fun s => P s› ⦄ X := ‹e› ⦃ ‹fun s => ∃ n: Nat, P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)› ⦄] := sorry
  end Term

  namespace Tactic
    example: ⦃(Assertion.lt "X" 5) ["X" ↦ "X" + 1], .assign "X" ("X" + 1), Assertion.lt "X" 5⦄ := by
      apply HoareTriple.assign

    example: ∃ P, ⦃P, .assign "X" (2 * "X"), "X" ≤ 10⦄ := by
      exists "X" ≤ 5
      sorry

    example: ∃ P, ⦃P, .assign "X" 3, ("X" ≤ 0 ∧ "X" ≤ 5)⦄ := by
      exists True
      sorry

    example: ∃ E: Arith, ¬ ⦃True, .assign "X" e, "X" === e⦄ := by
      sorry

    example (n: Nat) (e: Arith) (P: Assertion): ⦃fun s => P s ∧ s "X" = n, .assign "X" e, fun s => P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)⦄ := by
      sorry

    example (e: Arith) (P: Assertion): ⦃fun s => P s, .assign "X" e, fun s => ∃ n: Nat, P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)⦄ := by
      sorry
  end Tactic

  namespace Blended
    example: ⦃(Assertion.lt "X" 5) ["X" ↦ "X" + 1], .assign "X" ("X" + 1), Assertion.lt "X" 5⦄ :=
      HoareTriple.assign

    example: ∃ P, ⦃P, .assign "X" (2 * "X"), "X" ≤ 10⦄ := sorry
    example: ∃ P, ⦃P, .assign "X" 3, ("X" ≤ 0 ∧ "X" ≤ 5)⦄ := sorry
    example: ∃ E: Arith, ¬ ⦃True, .assign "X" e, "X" === e⦄ := sorry
    example (n: Nat) (e: Arith) (P: Assertion): ⦃fun s => P s ∧ s "X" = n, .assign "X" e, fun s => P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)⦄ := sorry
    example (e: Arith) (P: Assertion): ⦃fun s => P s, .assign "X" e, fun s => ∃ n: Nat, P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)⦄ := sorry
  end Blended

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
