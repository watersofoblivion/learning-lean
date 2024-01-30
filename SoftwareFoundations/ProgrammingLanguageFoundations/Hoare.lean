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

  @[reducible] def Assertion.prop (P: Prop): Assertion
    | _ => P
  @[reducible] def Assertion.implies (P Q: Assertion): Assertion
    | s => P s → Q s
  @[reducible] def Assertion.iff (P Q: Assertion): Assertion
    | s => P s ↔ Q s
  @[reducible] def Assertion.and (P Q: Assertion): Assertion
    | s => P s ∧ Q s
  @[reducible] def Assertion.or (P Q: Assertion): Assertion
    | s => P s ∨ Q s
  @[reducible] def Assertion.not (P: Assertion): Assertion
    | s => ¬ P s

  def NatAssertion: Type := State → Nat

  @[reducible] def NatAssertion.num (n: Nat): NatAssertion
    | _ => n
  @[reducible] def NatAssertion.id (id: String): NatAssertion
    | s => s id
  @[reducible] def NatAssertion.arith (e: Arith): NatAssertion
    | s => e.eval s

  @[reducible] def NatAssertion.plus (e₁ e₂: NatAssertion): NatAssertion
    | s => e₁ s + e₂ s
  @[reducible] def NatAssertion.minus (e₁ e₂: NatAssertion): NatAssertion
    | s => e₁ s - e₂ s
  @[reducible] def NatAssertion.mult (e₁ e₂: NatAssertion): NatAssertion
    | s => e₁ s * e₂ s

  @[reducible] def NatAssertion.app₁ (f: Nat → Nat) (e: NatAssertion): NatAssertion
    | s => f (e s)
  @[reducible] def NatAssertion.app₂ (f: Nat → Nat → Nat) (e₁ e₂: NatAssertion): NatAssertion
    | s => f (e₁ s) (e₂ s)

  @[reducible] def NatAssertion.eq (P Q: NatAssertion): Assertion
    | s => P s = Q s
  @[reducible] def NatAssertion.neq (P Q: NatAssertion): Assertion
    | s => P s ≠ Q s
  @[reducible] def NatAssertion.le (P Q: NatAssertion): Assertion
    | s => P s ≤ Q s
  @[reducible] def NatAssertion.lt (P Q: NatAssertion): Assertion
    | s => P s < Q s
  @[reducible] def NatAssertion.ge (P Q: NatAssertion): Assertion
    | s => P s ≥ Q s
  @[reducible] def NatAssertion.gt (P Q: NatAssertion): Assertion
    | s => P s > Q s

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
  syntax "‹num:" term "›" : nat_assert
  syntax "‹id:" term "›" : nat_assert
  syntax "‹arith:" arith "›" : nat_assert
  syntax "(" nat_assert ")" : nat_assert

  syntax "[NatAssert|" nat_assert "]" : term

  macro_rules
    | `([NatAssert| $n:num])                                       => `(NatAssertion.num $n)
    | `([NatAssert| ‹num: $n:term ›])                              => `(NatAssertion.num $(Lean.quote n))
    | `([NatAssert| $id:ident])                                    => `(NatAssertion.id $(Lean.quote (toString id.getId)))
    | `([NatAssert| ‹id: $id:term ›])                              => `(NatAssertion.id $(Lean.quote id))
    | `([NatAssert| ‹arith: $e:arith ›])                           => `(NatAssertion.arith [Arith| $e])
    | `([NatAssert| $x + $y])                                      => `(NatAssertion.plus [NatAssert| $x] [NatAssert| $y])
    | `([NatAssert| $x - $y])                                      => `(NatAssertion.minus [NatAssert| $x] [NatAssert| $y])
    | `([NatAssert| $x * $y])                                      => `(NatAssertion.mult [NatAssert| $x] [NatAssert| $y])
    | `([NatAssert| app₂ ‹ $f:term › $x:nat_assert $y:nat_assert]) => `(NatAssertion.app₂ $(Lean.quote f) [NatAssert| $x] [NatAssert| $y])
    | `([NatAssert| app₁ ‹ $f:term › $x:nat_assert])               => `(NatAssertion.app₁ $(Lean.quote f) [NatAssert| $x])
    | `([NatAssert| ( $a:nat_assert )])                            => `([NatAssert| $a])

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
    | `([Assert| ‹prop: $P:term › ])             => `(Assertion.prop $(Lean.quote P))
    | `([Assert| ‹ $P:term › ])                  => `($(Lean.quote P))
    | `([Assert| $P → $Q])                       => `(Assertion.implies [Assert| $P] [Assert| $Q])
    | `([Assert| $P ↔ $Q])                       => `(Assertion.iff     [Assert| $P] [Assert| $Q])
    | `([Assert| $P ∧ $Q])                       => `(Assertion.and     [Assert| $P] [Assert| $Q])
    | `([Assert| $P ∨ $Q])                       => `(Assertion.or      [Assert| $P] [Assert| $Q])
    | `([Assert| ¬ $P])                          => `(Assertion.not     [Assert| $P])
    | `([Assert| $P:nat_assert = $Q:nat_assert]) => `(NatAssertion.eq  [NatAssert| $P] [NatAssert| $Q])
    | `([Assert| $P:nat_assert ≠ $Q:nat_assert]) => `(NatAssertion.neq [NatAssert| $P] [NatAssert| $Q])
    | `([Assert| $P:nat_assert ≤ $Q:nat_assert]) => `(NatAssertion.le  [NatAssert| $P] [NatAssert| $Q])
    | `([Assert| $P:nat_assert < $Q:nat_assert]) => `(NatAssertion.lt  [NatAssert| $P] [NatAssert| $Q])
    | `([Assert| $P:nat_assert ≥ $Q:nat_assert]) => `(NatAssertion.ge  [NatAssert| $P] [NatAssert| $Q])
    | `([Assert| $P:nat_assert > $Q:nat_assert]) => `(NatAssertion.gt  [NatAssert| $P] [NatAssert| $Q])
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
    ∀ s₁ s₂: State, P s₁ → (s₁ =[c]=> s₂) → Q s₂

  @[reducible]
  def Assertion.subst (id: String) (e: Arith) (P: Assertion): Assertion
    | s => P (s.update id (e.eval s))

  syntax:40 assert "[" ident "↦" arith "]" : assert
  syntax:40 assert "[" "‹" term "›" "↦" arith "]" : assert
  syntax:40 assert "[" ident "↦" "‹" term "›" "]" : assert
  syntax:40 assert "[" "‹" term "›" "↦" "‹" term "›" "]" : assert

  macro_rules
    | `([Assert| $P:assert [ $id:ident ↦ $e:arith ]])       => `([Assert| $P].subst $(Lean.quote (toString id.getId)) [Arith| $e])
    | `([Assert| $P:assert [ $id:ident ↦ ‹ $e:term › ]])    => `([Assert| $P].subst $(Lean.quote (toString id.getId)) $(Lean.quote e))
    | `([Assert| $P:assert [ ‹ $id:term › ↦ $e:arith ]])    => `([Assert| $P].subst $(Lean.quote id) [Arith| $e])
    | `([Assert| $P:assert [ ‹ $id:term › ↦ ‹ $e:term › ]]) => `([Assert| $P].subst $(Lean.quote id) $(Lean.quote e))

  declare_syntax_cat hoare

  syntax "⦃" assert "⦄" cmd "⦃" assert "⦄" : hoare

  syntax "[Hoare|" hoare "]" : term

  macro_rules
    | `([Hoare| ⦃ $pre:assert ⦄ $c:cmd ⦃ $post:assert ⦄ ]) => `(HoareTriple [Assert| $pre] [Imp| $c] [Assert| $post])

  theorem HoareTriple.post_true {P Q: Assertion} {c: Command}: (h: (s: State) → Q s) → [Hoare| ⦃ ‹P› ⦄ ‹c› ⦃ ‹Q› ⦄]
    | h, _, _, _, _ => h _

  theorem HoareTriple.pre_false {P Q: Assertion} {c: Command}: (h: (s: State) → ¬P s) → [Hoare| ⦃ ‹P› ⦄ ‹c› ⦃ ‹Q› ⦄]
    | h, _, _, hp, _ => absurd hp (h _)

  /-
  ## Proof Rules
  -/

  /-
  ### Skip
  -/

  theorem  HoareTriple.skip {P: Assertion}: [Hoare| ⦃ ‹P› ⦄ skip ⦃ ‹P› ⦄]
    | _, _, hp, .skip _ => hp

  /-
  ### Sequencing
  -/

  theorem HoareTriple.seq {P Q R: Assertion} {c₁ c₂: Command} (h₁: [Hoare| ⦃ ‹Q› ⦄ ‹c₂› ⦃ ‹R› ⦄]) (h₂: [Hoare| ⦃ ‹P› ⦄ ‹c₁› ⦃ ‹Q› ⦄]): [Hoare| ⦃ ‹P› ⦄ ‹c₁›; ‹c₂› ⦃ ‹R› ⦄]
    | _, _, hp, .seq _ _ _ h₃ h₄ =>
      have hq := h₂ _ _ hp h₃
      h₁ _ _ hq h₄

  /-
  ### Assignment
  -/

  theorem HoareTriple.assign {Q: Assertion} {id: String} {e: Arith}: [Hoare| ⦃ ‹Q› [‹id› ↦ ‹e›]⦄ ‹id› := ‹e› ⦃ ‹Q› ⦄]
    | _, _, hq, .assign _ h =>
      have h :=
        calc Assertion.subst id e Q _
          _ = Q (LogicalFoundations.Maps.TotalMap.update _ id (Arith.eval _ e)) := rfl
          _ = Q (LogicalFoundations.Maps.TotalMap.update _ id _)                := congrArg Q (congrArg (LogicalFoundations.Maps.TotalMap.update _ id) h)
      -- TODO: Remove Tactic Block
      by rw [h] at hq; exact hq

  namespace Term
    example: [Hoare| ⦃(X < 5) [X ↦ X + 1]⦄ X := X + 1 ⦃X < 5⦄]
      | s₁, s₂, hq, hc =>
        by
          unfold Assertion.subst at hq
          unfold Arith.eval at hq
          unfold Arith.eval at hq
          unfold NatAssertion.lt at hq
          unfold NatAssertion.num at hq
          unfold NatAssertion.id at hq
          unfold NatAssertion.lt
          unfold NatAssertion.num
          unfold NatAssertion.id
          simp_all

          sorry

    example: ∃ P: Assertion, [Hoare| ⦃ ‹P› ⦄ X := 2 * X ⦃X ≤ 10⦄] :=
      have w := [Assert| X ≤ 5]
      have hw
      | _, _, hq, hc => sorry
      ⟨w, hw⟩

    example: ∃ P: Assertion, [Hoare| ⦃ ‹P› ⦄ X := 3 ⦃(X ≤ 0 ∧ X ≤ 5)⦄] :=
      have w := [Assert| ‹prop:True› ]
      have hw
      | _, _, hq, hc => sorry
      ⟨w, hw⟩

    example: ∃ E: Arith, ¬ [Hoare| ⦃ ‹prop: True› ⦄ X := ‹e› ⦃X = ‹arith:e›⦄] :=
      have w := sorry
      have hw := sorry
      ⟨w, hw⟩

    example (n: Nat) (e: Arith) (P: Assertion): [Hoare| ⦃ ‹P› ∧ X = ‹num:n› ⦄ X := ‹e› ⦃ ‹fun s => P.subst "X" e (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)› ⦄]
      | _, _, hq, hc =>
        sorry

    example (e: Arith) (P: Assertion): [Hoare| ⦃ ‹P› ⦄ X := ‹e› ⦃ ‹fun s => ∃ n: Nat, P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)› ⦄]
      | _, _, hq, hc =>
        sorry
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

  theorem HoareTriple.consequence {P₁ P₂ Q₁ Q₂: Assertion} {c: Command} (h₁: [Hoare| ⦃ ‹P₂› ⦄ ‹c› ⦃ ‹Q₂› ⦄]) (h₂: [Assert| ‹P₁› → ‹P₂›]) (h₃: [Assert| ‹Q₂› → ‹Q₁›]): [Hoare| ⦃ ‹P₁› ⦄ ‹c› ⦃ ‹Q₁› ⦄] :=
    sorry
    where
      pre {P₁ P₂ Q: Assertion} {c: Command} (h₁: [Hoare| ⦃ ‹P₂› ⦄ ‹c› ⦃ ‹Q› ⦄]) (h₂: [Assert| ‹P₁› → ‹P₂›]): [Hoare| ⦃ ‹P₁› ⦄ ‹c› ⦃ ‹Q› ⦄] := sorry
      post {P Q₁ Q₂: Assertion} {c: Command} (h₁: [Hoare| ⦃ ‹P› ⦄ ‹c› ⦃ ‹Q₂› ⦄]) (h₂: [Assert| ‹Q₂› → ‹Q₁›]): [Hoare| ⦃ ‹P› ⦄ ‹c› ⦃ ‹Q₁› ⦄] := sorry

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
