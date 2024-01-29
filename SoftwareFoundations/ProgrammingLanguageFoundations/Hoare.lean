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
  def ArithAssertion: Type := State → Arith

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

  instance: Coe Nat NatAssertion where
    coe n := fun _ => n
  instance: Coe String NatAssertion where
    coe id := fun s => s id
  instance: OfNat NatAssertion n where
    ofNat := (n: NatAssertion)
  instance: Coe Arith NatAssertion where
    coe e := fun s => e.eval s
  instance: Coe Prop Assertion where
    coe P := fun _ => P

  @[reducible]
  def Assertion.implies (P Q: Assertion): Assertion := fun s => P s → Q s
  def Assertion.iff (P Q: Assertion): Assertion := fun s => implies P Q s ∧ implies Q P s
  def Assertion.and (P Q: Assertion): Assertion := fun s => P s ∧ Q s
  def Assertion.or (P Q: Assertion): Assertion := fun s => P s ∨ Q s
  def Assertion.not (P: Assertion): Assertion := fun s => ¬ P s
  def Assertion.eq (P Q: NatAssertion): Assertion := fun s => P s = Q s
  def Assertion.neq (P Q: NatAssertion): Assertion := fun s => P s ≠ Q s
  def Assertion.lt (P Q: NatAssertion): Assertion := fun s => P s < Q s
  def Assertion.le (P Q: NatAssertion): Assertion := fun s => P s ≤ Q s
  def Assertion.gt (P Q: NatAssertion): Assertion := fun s => P s > Q s
  def Assertion.ge (P Q: NatAssertion): Assertion := fun s => P s ≥ Q s
  def Assertion.add (P Q: NatAssertion): NatAssertion := fun s => P s + Q s
  def Assertion.sub (P Q: NatAssertion): NatAssertion := fun s => P s - Q s
  def Assertion.mul (P Q: NatAssertion): NatAssertion := fun s => P s * Q s

  def ap (f: Nat → α) (e: NatAssertion) := fun s => f (e s)
  def ap₂ (f: Nat → Nat → a) (e₁ e₂: NatAssertion) := fun s => f (e₁ s) (e₂ s)

  infix:65 "→" => Assertion.implies
  infix:65 "↔" => Assertion.iff
  infixr:35 "∧" => Assertion.and
  infixr:30 "∨" => Assertion.or
  notation:max "¬" P:40 => Assertion.not P
  infix:50 "===" => Assertion.eq
  infix:65 "≠" => Assertion.neq
  infix:50 "<" => Assertion.lt
  infix:50 "≤" => Assertion.le
  infix:50 ">" => Assertion.gt
  infix:50 "≥" => Assertion.ge

  instance: Add NatAssertion where
    add P Q := Assertion.add P Q
  instance: Sub NatAssertion where
    sub P Q := Assertion.sub P Q
  instance: Mul NatAssertion where
    mul P Q := Assertion.mul P Q

  section
    private def ex₁: Assertion := "X" === 3
    private def ex₂: Assertion := True
    private def ex₃: Assertion := False

    private def ex₄: Assertion := "X" ≤ "Y"
    private def ex₅: Assertion := ("X" === 3) ∨ (("X": NatAssertion) < "Y")
    private def ex₆: Assertion := "X" === (ap₂ max "X" "Y")
    private def ex₇: Assertion := ("Z" * "Z" ≤ "X") ∨ ¬((ap Nat.succ "Z") * (ap Nat.succ "Z") ≤ "X")
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

  notation " ⦃ " P " , " c " , " Q " ⦄ " => HoareTriple P c Q

  theorem HoareTriple.post_true {P Q: Assertion} {c: Command}: (h: (s: State) → Q s) → ⦃P, c, Q⦄
    | h, s₁, s₂, hp, c =>
      sorry

  theorem HoareTriple.pre_false {P Q: Assertion} {c: Command}: (h: (s: State) → ¬P s) → ⦃P, c, Q⦄
    | h, s₁, s₂, hp, c => sorry

  /-
  ## Proof Rules
  -/

  /-
  ### Skip
  -/

  def HoareTriple.skip {P: Assertion}: ⦃P, .skip, P⦄
    | _, _, hp, .skip _ => hp

  /-
  ### Sequencing
  -/

  def HoareTriple.seq {P Q R: Assertion} {c₁ c₂: Command} (h₁: ⦃Q, c₂, R⦄) (h₂: ⦃P, c₁, Q⦄): ⦃P, (.seq c₁ c₂), R⦄
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

  def HoareTriple.assign {Q: Assertion} {id: String} {e: Arith}: ⦃Q [id ↦ e], (.assign id e), Q⦄
    | _,_, hqs, .assign _ h =>
      have h :=
        calc Assertion.subst id e Q _
          _ = Q (LogicalFoundations.Maps.TotalMap.update _ id (Arith.eval _ e)) := rfl
          _ = Q (LogicalFoundations.Maps.TotalMap.update _ id _)                := congrArg Q (congrArg (LogicalFoundations.Maps.TotalMap.update _ id) h)
      -- TODO: Remove Tactic Block
      by rw [h] at hqs; exact hqs

  namespace Term
    example: ⦃(Assertion.lt "X" 5) ["X" ↦ "X" + 1], .assign "X" ("X" + 1), Assertion.lt "X" 5⦄ :=
      HoareTriple.assign

    example: ∃ P, ⦃P, .assign "X" (2 * "X"), "X" ≤ 10⦄ :=
      ⟨"X" ≤ 5, sorry⟩

    example: ∃ P, ⦃P, .assign "X" 3, ("X" ≤ 0 ∧ "X" ≤ 5)⦄ :=
      ⟨True, sorry⟩

    example: ∃ E: Arith, ¬ ⦃True, .assign "X" e, "X" === e⦄ := sorry
    example (n: Nat) (e: Arith) (P: Assertion): ⦃fun s => P s ∧ s "X" = n, .assign "X" e, fun s => P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)⦄ := sorry
    example (e: Arith) (P: Assertion): ⦃fun s => P s, .assign "X" e, fun s => ∃ n: Nat, P (s.update "X" n) ∧ s "X" = e.eval (s.update "X" n)⦄ := sorry
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
