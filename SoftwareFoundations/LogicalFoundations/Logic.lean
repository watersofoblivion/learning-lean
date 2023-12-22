/-
# Logic
-/

import «SoftwareFoundations».«LogicalFoundations».«Tactics»

#check ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁
#check 2 = 2
#check 2 = 3
#check ∀ n: Nat, n = 2

theorem twoPlusTwoIsFour: 2 + 2 = 4 := by rfl
def plusClaim: Prop := 2 + 2 = 4
#check plusClaim

theorem plusClaimIsTrue: plusClaim := by rfl

def isThree (n: Nat): Prop := n = 3
#check isThree

def injective (f: α → β) := ∀ x₁ x₂: α, f x₁ = f x₂ → x₁ = x₂
theorem succInj: injective Nat.succ := by
  intros x₁ x₂ h
  injection h

#check Eq

/-
## Logical Connectives
-/

/-
### Conjunction
-/

example: 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  · rfl
  · rfl

theorem andExercise (n₁ n₂: Nat) (h: n₁ + n₂ = 0): n₁ = 0 ∧ n₂ = 0 := by
  apply And.intro
  · cases n₂ with
      | zero =>
        simp at h
        assumption
      | succ n₂ => contradiction
  · cases n₁ with
      | zero =>
        simp at h
        assumption
      | succ n₁ =>
        rw [Nat.add_comm] at h
        contradiction

theorem andExample2 (n₁ n₂: Nat) (h: n₁ = 0 ∧ n₂ = 0): n₁ + n₂ = 0 := by
  cases h; simp_all

theorem andExample3 (n₁ n₂: Nat) (h: n₁ + n₂ = 0): n₁ * n₂ = 0 := by
  cases andExercise n₁ n₂ h; simp_all

theorem proj1 (P Q: Prop) (h: P ∧ Q): P := by
  cases h; assumption

theorem proj2 (P Q: Prop) (h: P ∧ Q): Q := by
  cases h; assumption

theorem andComm (P Q: Prop) (h: P ∧ Q): Q ∧ P := by
  cases h with
    | intro p q => exact (And.intro q p)

theorem andAssoc (P Q R: Prop) (h: P ∧ (Q ∧ R)): (P ∧ Q) ∧ R := by
  cases h with
    | intro p h₂ =>
      cases h₂ with
        | intro q r => exact (And.intro (And.intro p q) r)

#check And

/-
### Disjunction
-/

theorem factorIsZero (n₁ n₂: Nat) (h: n₁ = 0 ∨ n₂ = 0): n₁ * n₂ = 0 := by
  cases h <;> simp_all

theorem orIntroLeft (A B: Prop) (h: A): A ∨ B := by
  apply Or.inl h

theorem zeroOrSucc (n: Nat): n = Nat.zero ∨ n = n.pred.succ := by
  sorry

theorem multIsZero (n₁ n₂: Nat) (h: n₁ * n₂ = 0): n₁ = 0 ∨ n₂ = 0 := by
  rw [←factorIsZero]
  repeat sorry

theorem orComm (P Q: Prop) (h: P ∨ Q): Q ∨ P := by
  cases h with
    | inl h => apply Or.inr h
    | inr h => apply Or.inl h

/-
### Falsehood and Negation
-/

theorem exFalsoQuodlibet (P: Prop) (h: False): P := by
  cases h

theorem notImpliesOurNot: ∀ P: Prop, ¬ P → (∀ Q: Prop, P → Q) := by
  intros
  contradiction

theorem zeroNotOne: ¬ (0 = 1) := by
  unfold Not
  intros
  contradiction

theorem notFalse: ¬ False := by
  unfold Not
  intros
  contradiction

theorem contradictionImpliesAnything (P Q: Prop) (h: P ∧ ¬ P): Q := by
  cases h; contradiction

theorem doubleNeg (P: Prop) (h: P): ¬¬P := by
  unfold Not
  intro h₂
  apply h₂ h

theorem contrapositive (P Q: Prop) (h: P → Q): ¬Q → ¬P := by
  unfold Not
  intro h₂
  intro h₃
  sorry

theorem notBothTrueAndFalse (P: Prop): ¬(P ∧ ¬P) := by
  unfold Not
  intro h
  sorry

theorem deMorganNotOr (P Q: Prop) (h: ¬(P ∨ Q)): ¬P ∧ ¬Q := by
  unfold Not at h
  sorry

theorem notTrueIsFalse (b: Bool) (h: ¬(b = true)): b = false := by
  cases b with
    | true => contradiction
    | false => simp

/-
### Truth
-/

def discrimFn: Nat → Prop
  | .zero => True
  | .succ _ => False

theorem discrimExample (n: Nat): ¬ (.zero = n.succ) := by
  intro h₁
  have h₂: discrimFn .zero := by
    simp
    -- apply True
    sorry
  rw [h₁] at h₂
  apply h₂

/-
### Logical Equivalence
-/

def iff (P Q: Prop) := (P → Q) ∧ (Q → P)

theorem iffSymm (P Q: Prop) (h: P ↔ Q): Q ↔ P := by
  apply Iff.intro <;> cases h <;> assumption

theorem notTrueIffFalse (b: Bool): ¬(b = true) ↔ b = false := by
  cases b <;> simp

theorem applyIffExample (P Q R: Prop) (h₁: P ↔ Q) (h₂: Q → R): P → R := by
  intro h₃
  apply h₂
  cases h₁ with
    | intro mp mpr =>
      apply mp
      assumption

theorem orDistributesOverAnd (P Q R: Prop): P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · cases h with
        | inl h => apply Or.inl h
        | inr h =>
          cases h with
            | intro l r => apply Or.inr l
    · cases h with
        | inl h => apply Or.inl h
        | inr h =>
          cases h with
            | intro l r => apply Or.inr r
  · intro h
    sorry

/-
### Setoids and Logical Equivalence
-/

theorem mulEqZero (n₁ n₂: Nat): n₁ * n₂ = 0 ↔ n₁ = 0 ∨ n₂ = 0 := by
  apply Iff.intro
  · apply multIsZero
  · apply factorIsZero

theorem orAssoc (P Q R: Prop): P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  apply Iff.intro
  · intro h
    cases h with
      | inl h =>
        apply Or.inl
        apply Or.inl
        assumption
      | inr h =>
        cases h with
          | inl h =>
            apply Or.inl
            apply Or.inr
            assumption
          | inr h =>
            apply Or.inr
            assumption
  · intro h
    cases h with
      | inl h =>
        cases h with
          | inl h =>
            apply Or.inl
            assumption
          | inr h =>
            apply Or.inr
            apply Or.inl
            assumption
      | inr h =>
        apply Or.inr
        apply Or.inr
        assumption

theorem mulEqZeroTernary (n₁ n₂ n₃: Nat): n₁ * n₂ * n₃ = 0 ↔ n₁ = 0 ∨ n₂ = 0 ∨ n₃ = 0 := by
  simp [mulEqZero, orAssoc]

/-
### Existential Quantification
-/

def Nat.evenProp (x: Nat): Prop := ∃ n: Nat, x = Nat.double n

theorem fourIsEven: Nat.evenProp 4 := by
  unfold Nat.evenProp
  exists 2

theorem existsExample2 (n₁: Nat) (h: ∃ n₂: Nat, n₁ = 4 + n₂): ∃ n₃, n₁ = 2 + n₃ := by
  have h₂: 2 + 2 = 4 := by rfl
  cases h with
    | intro w _ =>
      exists (2 + w)
      simp [← Nat.add_assoc, h₂]
      assumption

theorem distNotExists (P: α → Prop) (h: ∀ x: α, P x): ¬ (∃ y, ¬P y) := by
  unfold Not
  intro h₂
  cases h₂ with
    | intro w h₃ =>
      apply h₃
      apply h

theorem distExistsOr (P Q: α → Prop): (∃ x: α, P x ∨ Q x) ↔ (∃ x: α, P x) := by
  apply Iff.intro
  · intro h
    cases h with
      | intro w h =>
        sorry
  · intro h
    cases h with
      | intro w h =>
        sorry

theorem ltePlusExists (n₁ n₂: Nat) (h: n₁.less_eq n₂ = true): ∃ n₃: Nat, n₂ = n₁ + n₃ := by
  sorry

theorem plusExistsLte (n₁ n₂: Nat) (h: ∃ n₃, n₂ = n₁ + n₃): n₁.less_eq n₂ := by
  sorry

/-
## Programming with Propositions
-/

def List.mem (x: α): List α → Prop
  | [] => False
  | hd :: tl => hd = x ∨ tl.mem x

example: [1, 2, 3, 4, 5].mem 4 := by
  repeat unfold List.mem
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply Or.inl
  rfl

example (n₁: Nat) (h: [2, 4].mem n₁): ∃ n₂: Nat, n₁ = 2 * n₂ := by
  have h₂: 2 * 2 = 4 := by rfl
  cases h with
    | inl h =>
      exists 1
      simp_all
    | inr h =>
      cases h with
        | inl h =>
          exists 2
          simp [h₂]
          simp_all
        | inr h => contradiction

theorem memMap (f: α → β) (l: List α) (x: α) (h: l.mem x): (l.map f).mem (f x) := by
  induction l with
    | nil =>
      simp [List.map, List.mem]
      contradiction
    | cons hd tl ihₗ =>
      simp [List.map, List.mem]
      sorry

theorem memMapIff (f: α → β) (l: List α) (y: β): (l.map f).mem y ↔ ∃ x: α, f x = y ∧ l.mem x := by
  induction l with
    | nil =>
      simp [List.map, List.mem, Not]
      intro h
      cases h; assumption
    | cons hd tl ihₗ =>
      simp [List.map, List.mem]
      apply Iff.intro
      case mp =>
        intro h
        sorry
      case mpr =>
        intro h
        apply Or.inr
        rw [ihₗ]
        exists hd
        sorry

theorem memAppIff (l₁ l₂: List α) (x: α): (l₁.append l₂).mem x ↔ l₁.mem x ∨ l₂.mem x := by
  revert l₂
  induction l₁ with
    | nil =>
      intro l₂
      simp [List.append]
      apply Iff.intro
      · intro h
        apply Or.inr h
      · intro h
        cases h with
          | inl h => sorry
          | inr h => assumption
    | cons hd tl ihₗ =>
      intro l₂
      apply Iff.intro
      · intro h
        sorry
      · intro h
        simp [List.mem]
        apply Or.inr
        sorry

def List.every (P: α → Prop): List α → Prop
  | [] => True
  | hd :: tl => P hd ∧ tl.every P

theorem everyMem (P: α → Prop) (l: List α): (∀ x: α, l.mem x → P x) ↔ l.every P := by
  apply Iff.intro
  · intro h; sorry
  · intro h₁ x h₂
    sorry

def combineOddEven (Odd Even: Nat → Prop): Nat → Prop :=
  fun n => Odd n ∨ Even n

theorem combineOddEvenIntro (Odd Even: Nat → Prop) (n: Nat) (h₁: n.isOdd = true → Odd n) (h₂: n.isEven = true → Even n): combineOddEven Odd Even n := by
  sorry

theorem combineOddEvenElimOdd (Odd Even: Nat → Prop) (n: Nat) (h₁: combineOddEven Odd Even n) (h₂: n.isOdd = true): Odd n := by
  sorry

theorem combineOddEvenElimEven (Odd Even: Nat → Prop) (n: Nat) (h₁: combineOddEven Odd Even n) (h₂: n.isEven = true): Even n := by
  sorry

/-
## Applying Theorems to Arguments
-/

#check Add.mk
#check List.reverse
#check Nat.add_comm
#check ∀ n₁ n₂: Nat, n₁ + n₂ = n₂ + n₁

theorem Nat.addComm3 (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₃ + n₂) + n₁ := by
  rw [Nat.add_comm]
  have lem: n₂ + n₃ = n₃ + n₂ := by rw [Nat.add_comm]
  rw [lem]

theorem Nat.addComm3Take3 (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₃ + n₂) + n₁ := by
  rw [Nat.add_comm, Nat.add_comm n₂ n₃]

theorem isNotNil (x: α) (l: List α) (h: l.mem x): ¬(l = .nil) := by
  unfold Not
  intro h₂
  rw [h₂] at h
  simp [List.mem] at h

theorem isNotNil42 (l: List Nat) (h: l.mem 42): ¬(l = .nil) := by
  apply isNotNil 42
  assumption

example (n: Nat) (l: List Nat) (h: (l.map (fun n => n * 0)).mem n): n = 0 := by
  -- apply (proj1 _ _ (memMapIff _ _ _ _ _) h)
  sorry

/-
## Working with Decidable Properties
-/

example: Nat.isEven 42 = true := by rfl
example: Nat.evenProp 42 := by exists 21

theorem evenDouble (n: Nat): n.double.isEven = true := by
  induction n with
    | zero => simp
    | succ n ihₙ => simp [Nat.doubleIncr, Nat.isEven, ihₙ]

theorem evenDoubleConv (n₁: Nat): ∃ n₂: Nat, n₁ = if n₁.isEven then n₂.double else n₂.double.succ := by
  induction n₁ with
    | zero => exists 0
    | succ n ihₙ =>
      exists n
      simp [Nat.evenSucc]
      sorry

theorem evenBoolProp (n: Nat): n.isEven = true ↔ Nat.evenProp n := by
  apply Iff.intro
  · intro h
    cases n with
      | zero => exists 0
      | succ n =>
        rw [Nat.evenSucc] at h
        unfold Not at h
        sorry
  sorry

theorem eqbEq (n₁ n₂: Nat): n₁ == n₂ ↔ n₁ = n₂ := by
  apply Iff.intro
  · intro h
    simp at h
    assumption
  · intro h
    simp
    assumption

def Nat.isEvenPrime (n: Nat) := n == 2

example: Nat.evenProp 1000 := by exists 500
example: Nat.isEven 1000 = true := by rfl
example: Nat.evenProp 1000 := by
  rw [← evenBoolProp]
  rfl

example: Nat.isEven 1001 = false := by rfl
example: ¬(Nat.evenProp 1001) := by
  simp [←evenBoolProp, Nat.isEven]

theorem plusEqExample (n₁ n₂ n₃: Nat) (h: (n₁ == n₂) = true): (n₁ + n₃ == n₂ + n₃) = true := by
  rw [eqbEq] at h
  rw [h]
  simp

theorem andTrueIff (b₁ b₂: Bool): (b₁ && b₂) = true ↔ b₁ == true ∧ b₂ == true := by
  apply Iff.intro
  · intro h
    simp at h
    simp
    assumption
  · intro h
    simp at h
    simp
    assumption

theorem orTrueIff (b₁ b₂: Bool): (b₁ || b₂) = true ↔ b₁ == true ∨ b₂ == true := by
  apply Iff.intro
  · intro h
    simp at h
    simp
    assumption
  · intro h
    simp at h
    simp
    assumption

theorem eqbNeg (n₁ n₂: Nat): (n₁ == n₂) = false ↔ n₁ ≠ n₂ := by
  apply Iff.intro
  · unfold Ne Not
    intro h₁ h₂
    rw [← eqbEq] at h₂
    sorry
  · unfold Ne Not
    intro h₁
    rw [← eqbEq] at h₁
    sorry

def eqbList (eqb: α → α → Bool): List α → List α → Bool
  | [], [] => true
  | _, [] | [], _ => false
  | hd :: tl, hd' :: tl' => eqb hd hd' && eqbList eqb tl tl'

theorem eqbListTrueIff (eqb: α → α → Bool) (h₁: ∀ x₁ x₂: α, eqb x₁ x₂ = true ↔ x₁ = x₂): ∀ l₁ l₂: List α, eqbList eqb l₁ l₂ = true ↔ l₁ = l₂ := by
  intro l₁ l₂
  apply Iff.intro
  · intro h₂
    induction l₁ with
      | nil =>
        cases l₂ with
          | nil => rfl
          | cons hd tl => contradiction
      | cons hd tl ihₗ =>
        cases l₂ with
          | nil => contradiction
          | cons hd' tl' =>
            sorry
  · intro h₂
    induction l₁ with
      | nil =>
        cases l₂ with
          | nil => rfl
          | cons hd tl => contradiction
      | cons hd tl ihₗ =>
        cases l₂ with
          | nil => contradiction
          | cons hd' tl' =>
            sorry

def List.forAllB (p: α → Bool): List α → Bool
  | [] => true
  | hd :: tl => p hd && tl.forAllB p

theorem List.forAllTrueIff (p: α → Bool) (l: List α): l.forAllB p = true ↔ List.every (fun x => p x = true) l := by
  apply Iff.intro
  · intro h
    induction l with
      | nil =>
        simp [List.forAllB] at h
        assumption
      | cons hd tl ihₗ =>
        simp [List.forAllB] at h
        simp [List.every]
        cases h with
          | intro l r =>
            apply And.intro
            · assumption
            · apply ihₗ r
  · intro h
    induction l with
      | nil => simp [List.forAllB]
      | cons hd tl ihₗ =>
        simp [List.every] at h
        simp [List.forAllB]
        cases h with
          | intro l r =>
            apply And.intro
            · assumption
            · apply ihₗ r

/-
## The Logic of Lean (Coq)
-/

/-
### Functional Extensionality
-/

example: (fun x => 3 + x) = (fun x => (Nat.pred 4) + x) := by rfl
example (f g: α → β) (x: α) (h: f x = g x): f = g := by
  apply funext
  sorry

example: (fun x => x + 1) = (fun x => 1 + x) := by
  funext x
  rw [Nat.add_comm]

def List.revAppend: List α → List α → List α
  | [], [] => []
  | [], l₂ => l₂
  | hd :: tl, l₂ => tl.revAppend (hd :: l₂)

def List.tailRecRev (l: List α): List α :=
  l.revAppend []

theorem List.tailRecRevCorrect: List.reverse α = List.tailRecRev α := by
  simp [List.reverse, List.tailRecRev, List.reverseAux]
  sorry

def excludedMiddle (P: Prop): Prop := P ∨ ¬P

theorem restrictedExcludedMiddle (P: Prop) (b: Bool) (h: P ↔ b = true): P ∨ ¬P := by
  cases b with
    | true =>
      apply Or.inl
      rw [h]
    | false =>
      rw [h]
      simp

theorem restrictedExcludedMiddleEq (n₁ n₂: Nat): n₁ = n₂ ∨ n₁ ≠ n₂ := by
  apply (restrictedExcludedMiddle (n₁ = n₂) (n₁.eq n₂))
  -- rw [Iff.symm]
  -- apply eqbEq
  sorry

theorem excludedMiddleIrrefutable (P: Prop): ¬¬(P ∨ ¬P) := by
  unfold Not
  intro h
  sorry

theorem notExistsDist (P: α → Prop) (h: ¬(∃ x: α, ¬P x)): ∀ x: α, P x := by
  intro x
  unfold Not at h
  -- rw [excludedMiddle] at h
  sorry

def pierce: Prop := ∀ P Q: Prop, ((P → Q) → P) → P
def doubleNegationElimination: Prop := ∀ P: Prop, ¬¬P → P
def deMorganNotAndNot: Prop := ∀ P Q: Prop, ¬(¬P ∧ ¬Q) → P ∨ Q
def impliesToOr: Prop := ∀ P Q: Prop, (P → Q) → (¬P ∨ Q)

theorem unprovableEquiv (P Q: Prop): pierce → doubleNegationElimination → deMorganNotAndNot → impliesToOr := by
  intro a b c
  sorry
