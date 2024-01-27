/-
# Simple Imperative Programs
-/

import Mathlib.tactic.linarith

import «SoftwareFoundations».«LogicalFoundations».«Maps»

namespace SoftwareFoundations.LogicalFoundations.Imp
  /-
  ## Arithmetic and Boolean Expressions
  -/

  /-
  ### Syntax
  -/

  namespace AExp
    inductive Arith: Type where
      | num (n: Nat): Arith
      | plus (e₁ e₂: Arith): Arith
      | minus (e₁ e₂: Arith): Arith
      | mult (e₁ e₂: Arith): Arith

    @[reducible]
    def Arith.eval: Arith → Nat
      | .num n => n
      | .plus e₁ e₂ => e₁.eval + e₂.eval
      | .minus e₁ e₂ => e₁.eval - e₂.eval
      | .mult e₁ e₂ => e₁.eval * e₂.eval

    @[reducible]
    def Arith.optZeroPlus: Arith → Arith
      | .num n => .num n
      | .plus (.num 0) e₂ => e₂.optZeroPlus
      | .plus e₁ e₂ => .plus e₁.optZeroPlus e₂.optZeroPlus
      | .minus e₁ e₂ => .minus e₁.optZeroPlus e₂.optZeroPlus
      | .mult e₁ e₂ => .mult e₁.optZeroPlus e₂.optZeroPlus

    example: (Arith.plus (.num 2) (.num 2)).eval = 4 := rfl
    example: (Arith.plus (.num 2) (.plus (.num 0) (.plus (.num 0) (.num 1)))).optZeroPlus = .plus (.num 2) (.num 1) := rfl

    example: (a: Arith) → a.optZeroPlus.eval = a.eval
      | .num _ => rfl
      | .plus e₁ e₂ =>
        have ih₁: e₁.optZeroPlus.eval = e₁.eval := _example e₁
        have ih₂: e₂.optZeroPlus.eval = e₂.eval := _example e₂
        match e₁ with
          | .num n =>
            match n with
              | .zero =>
                calc (Arith.plus (.num 0) e₂).optZeroPlus.eval
                  _ = e₂.optZeroPlus.eval                := rfl
                  _ = e₂.eval                            := ih₂
                  _ = 0 + e₂.eval                        := Eq.symm (Nat.zero_add e₂.eval)
              | .succ n =>
                calc (Arith.plus (.num n.succ) e₂).optZeroPlus.eval
                  _ = (Arith.num n.succ).optZeroPlus.eval + e₂.optZeroPlus.eval := rfl
                  _ = (Arith.num n.succ).eval + e₂.eval                         := congr (congrArg Nat.add ih₁) ih₂
          | .plus _ _ =>
            calc (Arith.plus (Arith.plus _ _) e₂).optZeroPlus.eval
              _ = (Arith.plus _ _).optZeroPlus.eval + e₂.optZeroPlus.eval := rfl
              _ = (Arith.plus _ _).eval + e₂.eval                         := congr (congrArg Nat.add ih₁) ih₂
          | .minus _ _ =>
            calc (Arith.plus (Arith.minus _ _) e₂).optZeroPlus.eval
              _ = (Arith.minus _ _).optZeroPlus.eval + e₂.optZeroPlus.eval := rfl
              _ = (Arith.minus _ _).eval + e₂.eval                         := congr (congrArg Nat.add ih₁) ih₂
          | .mult _ _ =>
            calc (Arith.plus (Arith.mult _ _) e₂).optZeroPlus.eval
              _ = (Arith.mult _ _).optZeroPlus.eval + e₂.optZeroPlus.eval := rfl
              _ = (Arith.mult _ _).eval + e₂.eval                         := congr (congrArg Nat.add ih₁) ih₂
      | .minus e₁ e₂ =>
        have ih₁: e₁.optZeroPlus.eval = e₁.eval := _example e₁
        have ih₂: e₂.optZeroPlus.eval = e₂.eval := _example e₂
        calc (Arith.minus e₁ e₂).optZeroPlus.eval
          _ = e₁.optZeroPlus.eval - e₂.optZeroPlus.eval := rfl
          _ = e₁.eval - e₂.eval                         := congr (congrArg Nat.sub ih₁) ih₂
      | .mult e₁ e₂ =>
        have ih₁: e₁.optZeroPlus.eval = e₁.eval := _example e₁
        have ih₂: e₂.optZeroPlus.eval = e₂.eval := _example e₂
        calc (Arith.mult e₁ e₂).optZeroPlus.eval
          _ = e₁.optZeroPlus.eval * e₂.optZeroPlus.eval := rfl
          _ = e₁.eval * e₂.eval                         := congr (congrArg Nat.mul ih₁) ih₂
          _ = (Arith.mult e₁ e₂).eval                   := rfl

    theorem Arith.optZeroPlus.sound (a: Arith): a.optZeroPlus.eval = a.eval := by
      induction a with
        | num n => rfl
        | plus e₁ e₂ ih₁ ih₂ =>
          cases e₁ with
            | num n =>
              cases n with
                | zero => simp_all
                | succ n =>
                  unfold optZeroPlus eval
                  simp_all
            | plus | minus | mult =>
              unfold optZeroPlus eval
              simp_all
        | minus _ _ ih₁ ih₂ | mult _ _ ih₁ ih₂ =>
          unfold optZeroPlus eval
          simp_all

    example: (a: Arith) → a.optZeroPlus.eval = a.eval
      | .num _ => by rfl
      | .plus e₁ e₂ =>
        have ih₁: e₁.optZeroPlus.eval = e₁.eval := _example e₁
        have ih₂: e₂.optZeroPlus.eval = e₂.eval := _example e₂
        match e₁ with
          | .num n =>
            match n with
              | .zero =>
                calc (Arith.plus (.num 0) e₂).optZeroPlus.eval
                  _ = e₂.optZeroPlus.eval                := by rfl
                  _ = e₂.eval                            := by rw [ih₂]
                  _ = 0 + e₂.eval                        := by rw [Nat.zero_add]
              | .succ n =>
                calc (Arith.plus (.num n.succ) e₂).optZeroPlus.eval
                  _ = (Arith.num n.succ).optZeroPlus.eval + e₂.optZeroPlus.eval := by rfl
                  _ = (Arith.num n.succ).eval + e₂.eval                         := by rw [ih₁, ih₂]
          | .plus _ _ | .minus _ _ | .mult _ _ => by
            unfold Arith.eval
            rw [ih₁, ih₂]
      | .minus e₁ e₂ | .mult e₁ e₂ => by
        have ih₁: e₁.optZeroPlus.eval = e₁.eval := _example e₁
        have ih₂: e₂.optZeroPlus.eval = e₂.eval := _example e₂
        unfold Arith.eval
        rw [ih₁, ih₂]

    inductive Logic: Type where
      | true: Logic
      | false: Logic
      | eq (e₁ e₂: Arith): Logic
      | neq (e₁ e₂: Arith): Logic
      | le (e₁ e₂: Arith): Logic
      | gt (e₁ e₂: Arith): Logic
      | not (e: Logic): Logic
      | and (e₁ e₂: Logic): Logic

    @[reducible]
    def Logic.eval: Logic → Bool
      | .true => Bool.true
      | .false => Bool.false
      | .eq e₁ e₂ => e₁.eval == e₂.eval
      | .neq e₁ e₂ => e₁.eval != e₂.eval
      | .le e₁ e₂ => e₁.eval ≤ e₂.eval
      | .gt e₁ e₂ => e₁.eval > e₂.eval
      | .not e => !e.eval
      | .and e₁ e₂ => e₁.eval && e₂.eval

    @[reducible]
    def Logic.optZeroPlus: Logic → Logic
      | .true => .true
      | .false => .false
      | .eq e₁ e₂ => .eq e₁.optZeroPlus e₂.optZeroPlus
      | .neq e₁ e₂ => .neq e₁.optZeroPlus e₂.optZeroPlus
      | .le e₁ e₂ => .le e₁.optZeroPlus e₂.optZeroPlus
      | .gt e₁ e₂ => .gt e₁.optZeroPlus e₂.optZeroPlus
      | .not e => .not e.optZeroPlus
      | .and e₁ e₂ => .and e₁.optZeroPlus e₂.optZeroPlus

    /-
    ## Lean (Coq) Automation
    -/

    /-
    ### The `try` Tactical
    -/

    example (P: Prop) (h: P): P := by
      try rfl
      apply h

    example (a: Arith): a.eval = a.eval := by
      try rfl

    /-
    ### The `<;>` Tactical (Simple Form)
    -/

    example (n: Nat): 0 ≤ n := by
      cases n with
        | zero => simp
        | succ n => simp

    example (n: Nat): 0 ≤ n := by
      cases n <;> simp

    /-
    ### The `<;>` Tactical (General Form)
    -/

    example (a: Arith): a.optZeroPlus.eval = a.eval := by
      induction a <;>
      try (first | rfl
                 | unfold Arith.optZeroPlus Arith.eval
                   simp_all)
      case plus e₁ _ ih₁ ih₂ =>
        cases e₁ <;>
        try (unfold Arith.optZeroPlus Arith.eval
             rw [ih₁, ih₂])
        case num n =>
          cases n with
            | zero => simp_all
            | succ n =>
              unfold Arith.optZeroPlus Arith.eval
              simp_all

    /-
    ### The `repeat` Tactical
    -/

    def In (x: α) (l: List α): Prop :=
      match l with
        | [] => False
        | b :: m => b = x ∨ In x m

    example: In 10 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
      repeat (try (first | apply Or.inl; rfl | apply Or.inr))

    example: (b: Logic) → b.optZeroPlus.eval = b.eval
      | .true | .false => rfl
      | .eq e₁ e₂ =>
        have h₁ := Arith.optZeroPlus.sound e₁
        have h₂ := Arith.optZeroPlus.sound e₂
        calc (Logic.eq e₁ e₂).optZeroPlus.eval
          _ = BEq.beq e₁.optZeroPlus.eval e₂.optZeroPlus.eval := rfl
          _ = BEq.beq e₁.eval e₂.eval                         := congr (congrArg BEq.beq h₁) h₂
      | .neq e₁ e₂ =>
        have h₁ := Arith.optZeroPlus.sound e₁
        have h₂ := Arith.optZeroPlus.sound e₂
        calc (Logic.neq e₁ e₂).optZeroPlus.eval
          _ = not (BEq.beq e₁.optZeroPlus.eval e₂.optZeroPlus.eval) := rfl
          _ = not (BEq.beq e₁.eval e₂.eval)                         := congrArg not (congr (congrArg BEq.beq h₁) h₂)
      | .le e₁ e₂ =>
        have h₁ := Arith.optZeroPlus.sound e₁
        have h₂ := Arith.optZeroPlus.sound e₂
        calc (Logic.le e₁ e₂).optZeroPlus.eval
          _ = (LE.le e₁.optZeroPlus.eval e₂.optZeroPlus.eval: Bool) := rfl
          _ = (LE.le e₁.eval e₂.eval: Bool)                         := sorry -- congr (congrArg LE.le h₁) h₂
      | .gt e₁ e₂ =>
        have h₁ := Arith.optZeroPlus.sound e₁
        have h₂ := Arith.optZeroPlus.sound e₂
        calc (Logic.gt e₁ e₂).optZeroPlus.eval
          _ = (GT.gt e₁.optZeroPlus.eval e₂.optZeroPlus.eval: Bool) := rfl
          _ = (GT.gt e₁.eval e₂.eval: Bool)                         := sorry -- congr (congrArg LE.le h₁) h₂
      | .not b =>
        have ih := _example b
        calc (Logic.not b).optZeroPlus.eval
          _ = not b.optZeroPlus.eval := rfl
          _ = not b.eval             := congrArg not ih
      | .and b₁ b₂ =>
        have ih₁ := _example b₁
        have ih₂ := _example b₂
        calc (Logic.and b₁ b₂).optZeroPlus.eval
          _ = and b₁.optZeroPlus.eval b₂.optZeroPlus.eval := rfl
          _ = and b₁.eval b₂.eval                         := congr (congrArg and ih₁) ih₂

    theorem Logic.optZeroPlus.sound (e: Logic): e.optZeroPlus.eval = e.eval := by
      induction e <;>
      try (first | rfl
                 | unfold Logic.optZeroPlus Logic.eval
                   simp [Arith.optZeroPlus.sound])
      case not e ih =>
        unfold Logic.optZeroPlus Logic.eval
        rw [ih]
      case and e₁ e₂ ih₁ ih₂ =>
        unfold Logic.optZeroPlus Logic.eval
        rw [ih₁, ih₂]

    example: (b: Logic) → b.optZeroPlus.eval = b.eval
      | .true | .false => by rfl
      | .eq e₁ e₂ | .neq e₁ e₂ | .le e₁ e₂ | .gt e₁ e₂ => by
        have h₁ := Arith.optZeroPlus.sound e₁
        have h₂ := Arith.optZeroPlus.sound e₂
        unfold Logic.eval
        rw [h₁, h₂]
      | .not b => by
        have ih := _example b
        unfold Logic.eval
        rw [ih]
      | .and b₁ b₂ => by
        have ih₁ := _example b₁
        have ih₂ := _example b₂
        unfold Logic.eval
        rw [ih₁, ih₂]

    @[reducible]
    def Arith.constFold: Arith → Arith
      | .plus e₁ e₂ =>
        match e₁.constFold, e₂.constFold with
          | .num n₁, .num n₂ => .num (n₁ + n₂)
          | e₁, e₂ => .plus e₁ e₂
      | .minus e₁ e₂ =>
        match e₁.constFold, e₂.constFold with
          | .num n₁, .num n₂ => .num (n₁ - n₂)
          | e₁, e₂ => .minus e₁ e₂
      | .mult e₁ e₂ =>
        match e₁.constFold, e₂.constFold with
          | .num n₁, .num n₂ => .num (n₁ * n₂)
          | e₁, e₂ => .mult e₁ e₂
      | e => e

    -- MOAR OPTIMIZATION: Constant Folding

    -- TODO: Remove Tactic Blocks
    example: (e: Arith) → e.constFold.eval = e.eval
      | .num _ => rfl
      | .plus e₁ e₂ =>
        have ih₁ := _example e₁
        have ih₂ := _example e₂
        match h₁: e₁.constFold with
          | .num n₁ =>
            match h₂: e₂.constFold with
              | .num n₂ =>
                calc (Arith.plus e₁ e₂).constFold.eval
                  _ = (Arith.plus (Arith.num n₁) (Arith.num n₂)).eval := by unfold Arith.constFold; rw [h₁, h₂]
                  _ = (Arith.num n₁).eval + (Arith.num n₂).eval       := by rfl
                  _ = e₁.constFold.eval + e₂.constFold.eval           := by rw [h₁, h₂]
                  _ = e₁.eval + e₂.eval                               := by rw [ih₁, ih₂]
              | .plus _ _ =>
                calc (Arith.plus e₁ e₂).constFold.eval
                  _ = (Arith.plus (Arith.num n₁) (Arith.plus _ _)).eval := by unfold Arith.constFold; rw [h₁, h₂]
                  _ = (Arith.num n₁).eval + (Arith.plus _ _).eval       := by rfl
                  _ = e₁.constFold.eval + e₂.constFold.eval             := by rw [h₁, h₂]
                  _ = e₁.eval + e₂.eval                                 := by rw [ih₁, ih₂]
              | .minus _ _ =>
                calc (Arith.plus e₁ e₂).constFold.eval
                  _ = (Arith.plus (Arith.num n₁) (Arith.minus _ _)).eval := by unfold Arith.constFold; rw [h₁, h₂]
                  _ = (Arith.num n₁).eval + (Arith.minus _ _).eval       := by rfl
                  _ = e₁.constFold.eval + e₂.constFold.eval              := by rw [h₁, h₂]
                  _ = e₁.eval + e₂.eval                                  := by rw [ih₁, ih₂]
              | .mult _ _ =>
                calc (Arith.plus e₁ e₂).constFold.eval
                  _ = (Arith.plus (Arith.num n₁) (Arith.mult _ _)).eval := by unfold Arith.constFold; rw [h₁, h₂]
                  _ = (Arith.num n₁).eval + (Arith.mult _ _).eval       := by rfl
                  _ = e₁.constFold.eval + e₂.constFold.eval             := by rw [h₁, h₂]
                  _ = e₁.eval + e₂.eval                                 := by rw [ih₁, ih₂]
          | _ => sorry
      | _ => sorry

    theorem Arith.constFold.sound (e: Arith): e.constFold.eval = e.eval := by sorry

    example: (e: Arith) → e.constFold.eval = e.eval
      | .num _ => rfl
      | .plus e₁ e₂ =>
        have ih₁ := _example e₁
        have ih₂ := _example e₂
        match h₁: e₁.constFold with
          | .num n₁ =>
            match h₂: e₂.constFold with
              | .num n₂ =>
                calc (Arith.plus e₁ e₂).constFold.eval
                  _ = (Arith.plus (Arith.num n₁) (Arith.num n₂)).eval := by unfold Arith.constFold; rw [h₁, h₂]
                  _ = (Arith.num n₁).eval + (Arith.num n₂).eval       := by rfl
                  _ = e₁.constFold.eval + e₂.constFold.eval           := by rw [h₁, h₂]
                  _ = e₁.eval + e₂.eval                               := by rw [ih₁, ih₂]
              | .plus _ _ =>
                calc (Arith.plus e₁ e₂).constFold.eval
                  _ = (Arith.plus (Arith.num n₁) (Arith.plus _ _)).eval := by unfold Arith.constFold; rw [h₁, h₂]
                  _ = (Arith.num n₁).eval + (Arith.plus _ _).eval       := by rfl
                  _ = e₁.constFold.eval + e₂.constFold.eval             := by rw [h₁, h₂]
                  _ = e₁.eval + e₂.eval                                 := by rw [ih₁, ih₂]
              | .minus _ _ =>
                calc (Arith.plus e₁ e₂).constFold.eval
                  _ = (Arith.plus (Arith.num n₁) (Arith.minus _ _)).eval := by unfold Arith.constFold; rw [h₁, h₂]
                  _ = (Arith.num n₁).eval + (Arith.minus _ _).eval       := by rfl
                  _ = e₁.constFold.eval + e₂.constFold.eval              := by rw [h₁, h₂]
                  _ = e₁.eval + e₂.eval                                  := by rw [ih₁, ih₂]
              | .mult _ _ =>
                calc (Arith.plus e₁ e₂).constFold.eval
                  _ = (Arith.plus (Arith.num n₁) (Arith.mult _ _)).eval := by unfold Arith.constFold; rw [h₁, h₂]
                  _ = (Arith.num n₁).eval + (Arith.mult _ _).eval       := by rfl
                  _ = e₁.constFold.eval + e₂.constFold.eval             := by rw [h₁, h₂]
                  _ = e₁.eval + e₂.eval                                 := by rw [ih₁, ih₂]
          | _ => sorry
      | _ => sorry


    def Logic.constFold: Logic → Logic
      | .eq e₁ e₂ =>
        match e₁.constFold, e₂.constFold with
          | .num n₁, .num n₂ => if n₁ == n₂ then .true else .false
          | e₁, e₂ => .eq e₁ e₂
      | .neq e₁ e₂ =>
        match e₁.constFold, e₂.constFold with
          | .num n₁, .num n₂ => if n₁ != n₂ then .true else .false
          | e₁, e₂ => .neq e₁ e₂
      | .le e₁ e₂ =>
        match e₁.constFold, e₂.constFold with
          | .num n₁, .num n₂ => if n₁ ≤ n₂ then .true else .false
          | e₁, e₂ => .le e₁ e₂
      | .gt e₁ e₂ =>
        match e₁.constFold, e₂.constFold with
          | .num n₁, .num n₂ => if n₁ > n₂ then .true else .false
          | e₁, e₂ => .gt e₁ e₂
      | .not b =>
        match b.constFold with
          | .true => .false
          | .false => .true
          | b => .not b
      | .and b₁ b₂ =>
        match b₁.constFold, b₂.constFold with
          | .true, .true => .true
          | .true, .false | .false, .true | .false, .false => .false
          | b₁, b₂ => .and b₁ b₂
      | b => b

    example: (b: Logic) → b.constFold.eval = b.eval := sorry
    theorem Logic.constFold.sound (b: Logic): b.constFold.eval = b.eval := by sorry
    example: (b: Logic) → b.constFold.eval = b.eval := sorry

    /-
    ## Defining New Tactics
    -/

    -- TODO: Research defining tactics in Lean

    /-
    ## The `linearith` (`lia`) Tactic
    -/

    -- import Mathlib.tactics.linarith

    example (n₁ n₂ n₃ n₄: Nat) (h: n₁ + n₂ ≤ n₂ + n₃ ∧ n₃ + 3 = n₄ + 3): n₁ ≤ n₄ := by
      linarith

    example (n₁ n₂: Nat): n₁ + n₂ = n₂ + n₁ := by
      linarith

    example (n₁ n₂ n₃: Nat): n₁ + (n₂ + n₃) = (n₁ + n₂) + n₃ := by
      linarith

    /-
    ## A Few More Handy Tactics
    -/

    -- TODO: Research the same tactics in Lean

    /-
    ## Evaluation as a Relation
    -/

    inductive ArithEval: Arith → Nat → Prop where
      | num (n: Nat): ArithEval (.num n) n
      | plus (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.plus e₁ e₂) (n₁ + n₂)
      | minus (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.minus e₁ e₂) (n₁ - n₂)
      | mult (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.mult e₁ e₂) (n₁ * n₂)

    /-
    ### Inference Rule Notation
    -/

    inductive LogicEval: Logic → Bool → Prop where
      | true: LogicEval .true true
      | false: LogicEval .false false
      | eq (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): LogicEval (.eq e₁ e₂) (n₁ == n₂)
      | neq (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): LogicEval (.neq e₁ e₂) (n₁ != n₂)
      | le (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): LogicEval (.neq e₁ e₂) (n₁ ≤ n₂)
      | gt (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): LogicEval (.neq e₁ e₂) (n₁ > n₂)
      | not (e: Logic) (b: Bool) (h: LogicEval e b): LogicEval (.not e) !b
      | and (e₁ e₂: Logic) (b₁ b₂: Bool) (h₁: LogicEval e₁ b₁) (h₂: LogicEval e₂ b₂): LogicEval (.and e₁ e₂) (b₁ && b₂)

    /-
    ### Equivalence of Definitions
    -/

    example {e: Arith} {n: Nat}: ArithEval e n ↔ e.eval = n :=
      ⟨mp, mpr⟩
      where
        mp {e: Arith} {n: Nat}: ArithEval e n → e.eval = n
          | .num n => rfl
          | .plus _ _ _ _ h₁ h₂ => mpf (mp h₁) (mp h₂) Nat.add rfl
          | .minus _ _ _ _ h₁ h₂ => mpf (mp h₁) (mp h₂) Nat.sub rfl
          | .mult _ _ _ _ h₁ h₂ => mpf (mp h₁) (mp h₂) Nat.mul rfl
        mpf {e e₁ e₂: Arith} {n₁ n₂: Nat} (ih₁: e₁.eval = n₁) (ih₂: e₂.eval = n₂) (f: Nat → Nat → Nat) (h: e.eval = f e₁.eval e₂.eval) :=
          calc e.eval
              _ = f (Arith.eval e₁) (Arith.eval e₂) := h
              _ = f n₁ n₂                           := congr (congrArg f ih₁) ih₂
        mpr {e: Arith} {n: Nat} (h: e.eval = n): ArithEval e n := sorry
          -- match e with
          --   | Arith.num _ => sorry --ArithEval.num _
          --   | Arith.plus e₁ e₂ =>
          --     have ih₁: sorry := sorry --mpr _
          --     have ih₂: sorry := sorry --mpr _
          --     sorry
          --   | _ => sorry

    theorem arith_eval_eval (a: Arith) (n: Nat): ArithEval a n ↔ a.eval = n := by
      apply Iff.intro
      · intro h
        induction h <;> first | rfl
                              | unfold Arith.eval
                                simp_all
      · intro h₁
        -- generalize n = q
        induction a with
          | num n =>
            rw [← h₁]
            apply ArithEval.num
          | plus e₁ e₂ ih₁ ih₂ =>
            -- unfold Arith.eval at h₁
            sorry
          | _ => sorry

    theorem logic_eval_eval (l: Logic) (b: Bool): LogicEval l b ↔ l.eval = b := by
      apply Iff.intro
      · intro h
        induction h with
          | true => rfl
          | false => rfl
          | eq e₁ e₂ n₁ n₂ h₁ h₂ =>
            unfold Logic.eval
            rw [arith_eval_eval] at *
            simp_all
          | neq e₁ e₂ n₁ n₂ h₁ h₂ =>
            unfold Logic.eval
            rw [arith_eval_eval] at *
            simp_all
          | le e₁ e₂ n₁ n₂ h₁ h₂ =>
            unfold Logic.eval
            rw [arith_eval_eval] at *
            simp_all
            sorry
          | gt e₁ e₂ n₁ n₂ h₁ h₂ =>
            unfold Logic.eval
            rw [arith_eval_eval] at *
            simp_all
            sorry
          | not e b h ih =>
            unfold Logic.eval
            rw [ih]
          | and e₁ e₂ b₁ b₂ h₁ h₂ ih₁ ih₂ =>
            unfold Logic.eval
            rw [ih₁, ih₂]
      · intro h
        induction l with
          | true =>
            cases b with
              | true => exact LogicEval.true
              | false => contradiction
          | false =>
            cases b with
              | true => contradiction
              | false => exact LogicEval.false
          | eq e₁ e₂ =>
            unfold Logic.eval at h
            sorry
          -- Other Arith cases
          | not e ih => sorry
          | and e₁ e₂ ih₁ ih₂ => sorry
          | _ => sorry
  end AExp

  namespace Division
    inductive Arith: Type where
      | num (n: Nat): Arith
      | plus (e₁ e₂: Arith): Arith
      | minus (e₁ e₂: Arith): Arith
      | mult (e₁ e₂: Arith): Arith
      | div (e₁ e₂: Arith): Arith

    inductive ArithEval: Arith → Nat → Prop where
      | num (n: Nat): ArithEval (.num n) n
      | plus (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.plus e₁ e₂) (n₁ + n₂)
      | minus (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.minus e₁ e₂) (n₁ - n₂)
      | mult (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.mult e₁ e₂) (n₁ * n₂)
      | div (e₁ e₂: Arith) (n₁ n₂ n₃: Nat) (nonZero: n₂ ≠ 0) (prod: n₂ * n₃ = n₁) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.div e₁ e₂) n₃
  end Division

  namespace Any
    inductive Arith: Type where
      | any: Arith
      | num (n: Nat): Arith
      | plus (e₁ e₂: Arith): Arith
      | minus (e₁ e₂: Arith): Arith
      | mult (e₁ e₂: Arith): Arith

    inductive ArithEval: Arith → Nat → Prop where
      | any (n: Nat): ArithEval .any n
      | num (n: Nat): ArithEval (.num n) n
      | plus (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.plus e₁ e₂) (n₁ + n₂)
      | minus (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.minus e₁ e₂) (n₁ - n₂)
      | mult (e₁ e₂: Arith) (n₁ n₂: Nat) (h₁: ArithEval e₁ n₁) (h₂: ArithEval e₂ n₂): ArithEval (.mult e₁ e₂) (n₁ * n₂)
  end Any

  /-
  ## Expressions with Variables
  -/

  def State: Type := Maps.TotalMap Nat

  def State.empty: State := Maps.TotalMap.empty 0

  @[reducible]
  def State.build (l: List (String × Nat)): State :=
    fold State.empty l
    where
      fold (s: State): List (String × Nat) → State
        | [] => s
        | (k, v) :: tl => fold (s.update k v) tl

  inductive Arith: Type where
    | num (n: Nat): Arith
    | ident (id: String): Arith
    | plus (e₁ e₂: Arith): Arith
    | minus (e₁ e₂: Arith): Arith
    | mult (e₁ e₂: Arith): Arith
  deriving DecidableEq

  inductive Logic: Type where
    | true: Logic
    | false: Logic
    | eq (e₁ e₂: Arith): Logic
    | neq (e₁ e₂: Arith): Logic
    | le (e₁ e₂: Arith): Logic
    | gt (e₁ e₂: Arith): Logic
    | not (e: Logic): Logic
    | and (e₁ e₂: Logic): Logic
  deriving DecidableEq

  /-
  ### Notations
  -/

  -- TODO: Implement syntax extensions (https://leanprover.github.io/lean4/doc/macro_overview.html)

  instance: Coe Bool Logic where
    coe: Bool → Logic
      | true => Logic.true
      | false => Logic.false
  instance: Coe Nat Arith where
    coe n := Arith.num n
  instance: OfNat Arith n where
    ofNat := Arith.num n
  instance: Coe String Arith where
    coe id := Arith.ident id

  instance: Add Arith where
    add x y := Arith.plus x y
  instance: Sub Arith where
    sub x y := Arith.minus x y
  instance: Mul Arith where
    mul x y := Arith.mult x y

  instance: Neg Logic where
    neg x := Logic.not x

  /-
  ### Evaluation
  -/

  @[reducible]
  def Arith.eval (state: State): Arith → Nat
    | num n => n
    | ident id => state id
    | plus e₁ e₂ => (e₁.eval state) + (e₂.eval state)
    | minus e₁ e₂ => (e₁.eval state) - (e₂.eval state)
    | mult e₁ e₂ => (e₁.eval state) * (e₂.eval state)

  @[reducible]
  def Logic.eval (state: State): Logic → Bool
    | true => Bool.true
    | false => Bool.false
    | eq e₁ e₂ => (e₁.eval state) == (e₂.eval state)
    | neq e₁ e₂ => (e₁.eval state) != (e₂.eval state)
    | le e₁ e₂ => (e₁.eval state) ≤ (e₂.eval state)
    | gt e₁ e₂ => (e₁.eval state) > (e₂.eval state)
    | not e => !(e.eval state)
    | and e₁ e₂ => (e₁.eval state) && (e₂.eval state)

  example: ((3: Arith) + "X" * 2).eval (State.build [("X", 5)]) = 13 := rfl
  example: (("Z": Arith) + "X" * "Y").eval (State.build [("X", 5), ("Y", 4)]) = 20 := rfl
  example: (Logic.and true (.not (.le "X" 4))).eval (State.build [("X", 5)]) = true := rfl

  /-
  ## Commands
  -/

  inductive Command: Type where
    | skip: Command
    | assign (id: String) (e: Arith): Command
    | seq (c₁ c₂: Command): Command
    | if (b: Logic) (c₁ c₂: Command): Command
    | while (b: Logic) (c: Command): Command

  instance: Coe (List Command) Command where
    coe l :=
      let rec conv: List Command → Command
        | [] => .skip
        | hd::[] => hd
        | hd::tl => .seq hd (conv tl)
      conv l

  def factorial: Command :=
    [
      (Command.assign "Z" "X"),
      (.assign "Y" 1),
      (.while (.neq "Z" 0) [
        (Command.assign "Y" ("Y" * "Z")),
        (.assign "Z" ("Z" - 1))
      ])
    ]

  /-
  ### Desugaring Notations
  -/

  set_option pp.notation true
  set_option pp.coercions false

  #print factorial

  set_option pp.notation false
  set_option pp.coercions true

  /-
  ### Locate, Again
  -/

  -- Appears to be Coq specific

  /- #### Finding Identifiers -/
  /- #### Finding Notations -/

  /-
  ### More Examples
  -/

  section
    /- #### Assignment -/

    def plus2: Command := .assign "X" ("X" + 2)
    def xTimesYInZ: Command := .assign "Z" ("X" * "Y")

    /- #### Loops -/

    private def subtractSlowlyBody: Command := ([
      (.assign "Z" ("Z" - 1)),
      (.assign "X" ("X" - 1))
    ]: List Command)

    private def subtractSlowly: Command :=
      .while (.neq "X" 0) subtractSlowlyBody

    private def subtract3From5Slowly: Command := ([
      (.assign "X" 3),
      (.assign "Z" 5),
      subtractSlowly
    ]: List Command)

    /- #### An Infinite Loop -/

    def loopForever: Command := .while .true .skip
  end

  /-
  ## Evaluating Commands
  -/

  def Command.noBueno (state: State): Command → State
    | .skip => state
    | .assign id e => state.update id (e.eval state)
    | .seq c₁ c₂ =>
      state
        |> c₁.noBueno
        |> c₂.noBueno
    | .if c t f =>
      if c.eval state
      then t.noBueno state
      else f.noBueno state
    | .while _ _ => state

  /-
  ### Evaluation as a Relation
  -/

  inductive CommandEval: Command → State → State → Prop where
    | skip (s: State): CommandEval .skip s s
    | assign {e: Arith} {n: Nat} {id: String} (s: State) (h: e.eval s = n): CommandEval (.assign id e) s (s.update id n)
    | seq {c₁ c₂: Command} (s₁ s₂ s₃: State) (h₁: CommandEval c₁ s₁ s₂) (h₂: CommandEval c₂ s₂ s₃): CommandEval (.seq c₁ c₂) s₁ s₃
    | ifTrue {c: Logic} {t f: Command} (s₁ s₂: State) (h₁: c.eval s₁ = .true) (h₂: CommandEval t s₁ s₂): CommandEval (.if c t f) s₁ s₂
    | ifFalse {c: Logic} {t f: Command} (s₁ s₂: State) (h₁: c.eval s₁ = .false) (h₂: CommandEval f s₁ s₂): CommandEval (.if c t f) s₁ s₂
    | whileTrue {c: Logic} {b: Command} (s₁ s₂ s₃: State) (h₁: c.eval s₁ = .true) (h₂: CommandEval b s₁ s₂) (h₃: CommandEval (.while c b) s₂ s₃): CommandEval (.while c b) s₁ s₃
    | whileFalse {c: Logic} {b: Command} (s: State) (h₁: c.eval s = .false): CommandEval (.while c b) s s

  def assignment (id: String) (n: Nat) (s: State): CommandEval (Command.assign id (n: Arith)) s (s.update id n) :=
      have h: (n: Arith).eval s = n := by
        unfold Arith.eval
        rfl
      CommandEval.assign s h

  section
    /- Useful definitions to save typing -/

    private def x0: Command := .assign "X" 0
    private def x2: Command := .assign "X" 2
    private def y1: Command := .assign "Y" 1
    private def y3: Command := .assign "Y" 3
    private def z2: Command := .assign "Z" 2
    private def z4: Command := .assign "Z" 4

    private def xLe1: Logic := .le "X" 1

    private def branch: Command := Command.if xLe1 y3 z4

    /- Example -/

    /- x := 2; if x ≤ 1 then y := 3 else z := 4 -/
    example: CommandEval [x2, branch] State.empty (State.build [("X", 2), ("Z", 4)]) :=
      let s₁: State := State.empty
      let s₂: State := s₁.update "X" 2
      let s₃: State := s₂.update "Z" 4

      have h₁: CommandEval x2 s₁ s₂ := assignment "X" 2 s₁
      have h₂: CommandEval branch s₂ s₃ :=
        have h₁: (Logic.le "X" 1).eval s₂ = false := by
          unfold Logic.eval
          rfl
        have h₂: CommandEval z4 s₂ s₃ := assignment "Z" 4 s₂
        CommandEval.ifFalse s₂ s₃ h₁ h₂

      by
        repeat unfold instCoeListCommand.conv
        exact CommandEval.seq s₁ s₂ s₃ h₁ h₂

    /- x := 0; y := 1; z := 2 -/
    example: CommandEval [x0, y1, z2] State.empty (State.build [("X", 0), ("Y", 1), ("Z", 2)]) :=
      let s₁: State := State.empty
      let s₂: State := s₁.update "X" 0
      let s₃: State := s₂.update "Y" 1
      let s₄: State := s₃.update "Z" 2

      by
        repeat unfold instCoeListCommand.conv
        sorry

    def sum: Command :=
      Command.seq
        (.assign "Y" 0)
        (.while (.gt "X" 0)
          (.seq (.assign "Y" ("X" + "Y"))
                (.assign "X" ("X" - 1))))

    example: CommandEval sum (State.build [("X", 2)]) (State.build [("X", 2), ("Y", 0), ("Y", 2), ("X", 1), ("Y", 3), ("X", 0)]) :=
      sorry
  end

  /-
  ### Determinism of Evaluation
  -/

  theorem CommandEval.deterministic (c: Command) (s₁ s₂ s₃: State) (h₁: CommandEval c s₁ s₂) (h₂: CommandEval c s₁ s₃): s₂ = s₃ := by
    sorry

  /-
  ## Reasoning about Imp Programs
  -/

  example (s₁ s₂: State) (n: Nat) (h₁: s₁ "X" = n) (h₂: CommandEval plus2 s₁ s₂): s₂ "X" = n + 2 := by
    cases h₂ with
      | assign _ h =>
        simp
        repeat unfold Arith.eval at h
        rw [h₁] at h
        apply Eq.symm
        exact h

  example (s₁ s₂: State) (n₁ n₂: Nat) (h₁: s₁ "X" = n₁) (h₂: s₁ "Y" = n₂) (h₃: CommandEval xTimesYInZ s₁ s₂): s₂ "Z" = n₁ * n₂ := by
    cases h₃ with
      | assign _ h =>
        repeat unfold Arith.eval at h
        repeat unfold Arith.eval at h
        rw [h₁, h₂] at h
        simp_all

  example (s₁ s₂: State): ¬CommandEval loopForever s₁ s₂ := by
    unfold Not
    intro h
    unfold loopForever at h
    cases h with
      | whileTrue h₁ h₂ h₃ => sorry
      | whileFalse h₁ => contradiction

  def Command.noWhiles: Command → Bool
    | .skip | .assign _ _ | .seq _ _ | .if _ _ _ => true
    | _ => false

  inductive NoWhiles: Command → Prop where
    | skip: NoWhiles .skip
    | assign {id: String} {e: Arith}: NoWhiles (.assign id e)
    | seq {c₁ c₂: Command}: NoWhiles (.seq c₁ c₂)
    | if {c: Logic} {t f: Command}: NoWhiles (.if c t f)

  theorem NoWhiles.noWhiles (c: Command): c.noWhiles = true ↔ NoWhiles c := by
    sorry

  theorem CommandEval.noWhiles_terminate (s₁ s₂: State) (c: Command) (h: NoWhiles c): CommandEval c s₁ s₂ := by
    sorry

  /-
  ## Additional Exercises
  -/

  abbrev Stack: Type := List Nat

  def Stack.empty: Stack := []

  inductive StackInstr: Type where
    | push (n: Nat): StackInstr
    | load (id: String): StackInstr
    | plus: StackInstr
    | minus: StackInstr
    | mult: StackInstr

  @[reducible]
  def StackInstr.eval (state: State): StackInstr → Stack → Stack
    | .push n, stack => n :: stack
    | .load id, stack => (state id) :: stack
    | .plus, r :: l :: stack => (l + r) :: stack
    | .minus, r :: l :: stack => (l - r) :: stack
    | .mult, r :: l :: stack => (l * r) :: stack
    | _, stack => stack

  abbrev Program: Type := List StackInstr

  @[reducible]
  def Program.eval (state: State) (program: Program) (init: Stack): Stack :=
    program.foldl (fun stack instr => instr.eval state stack) init

  example: Program.eval State.empty [StackInstr.push 5, .push 3, .push 1, .minus] Stack.empty = [2, 5] := by rfl
  example: Program.eval (State.build [("X", 3)]) [StackInstr.push 4, .load "X", .mult, .plus] [3, 4] = [15, 4] := rfl

  @[reducible]
  def Arith.compile: Arith → Program
    | .num n => [.push n]
    | .ident id => [.load id]
    | .plus e₁ e₂ => e₁.compile ++ e₂.compile ++ [.plus]
    | .minus e₁ e₂ => e₁.compile ++ e₂.compile ++ [.minus]
    | .mult e₁ e₂ => e₁.compile ++ e₂.compile ++ [.mult]

  example: (Arith.minus "X" (.mult 2 "Y")).compile = [StackInstr.load "X", .push 2, .load "Y", .mult, .minus] := rfl

  theorem eval_append (state: State) (p₁ p₂: Program) (stack: Stack): (p₁ ++ p₂).eval state stack = p₂.eval state (p₁.eval state stack) := by
    sorry

  theorem Arith.compile.correct (state: State) (e: Arith): e.compile.eval state Stack.empty = [e.eval state] := by
    sorry
    where
    helper (state: State) (stack: Stack) (e: Arith): e.compile.eval state stack = e.eval state :: stack := by
      sorry

  @[reducible]
  def Logic.shortCircuitEval (state: State): Logic → Bool
    | .and e₁ e₂ =>
      if e₁.eval state
      then Bool.true
      else e₂.eval state
    | l => l.eval state

  theorem Logic.shortCircuitEval.eval (state: State) (b: Logic): b.shortCircuitEval state = b.eval state := by
    induction b
    <;> try rfl
    case and e₁ e₂ h₁ h₂ =>
      sorry

  namespace BreakImp
    inductive Command: Type where
      | skip: Command
      | break: Command
      | assign (id: String) (e: Arith): Command
      | seq (c₁ c₂: Command): Command
      | if (b: Logic) (c₁ c₂: Command): Command
      | while (b: Logic) (c: Command): Command

    inductive Result: Type where
      | continue: Result
      | break: Result

    inductive CommandEval: Command → State → Result → State → Prop where
      | skip (s: State): CommandEval .skip s .continue s
      | break (s: State): CommandEval .break s .break s
      | assign {e: Arith} {n: Nat} {id: String} (s: State) (h: e.eval s = n): CommandEval (.assign id e) s .continue (s.update id n)
      | seq {c₁ c₂: Command} (s₁ s₂ s₃: State) (h₁: CommandEval c₁ s₁ .continue s₂) (h₂: CommandEval c₂ s₂ .continue s₃): CommandEval (.seq c₁ c₂) s₁ .continue s₃
      | ifTrue {c: Logic} {t f: Command} (s₁ s₂: State) (h₁: c.eval s₁ = .true) (h₂: CommandEval t s₁ .continue s₂): CommandEval (.if c t f) s₁ .continue s₂
      | ifFalse {c: Logic} {t f: Command} (s₁ s₂: State) (h₁: c.eval s₁ = .false) (h₂: CommandEval f s₁ .continue s₂): CommandEval (.if c t f) s₁ .continue s₂
      | whileTrue {c: Logic} {b: Command} (s₁ s₂ s₃: State) (h₁: c.eval s₁ = .true) (h₂: CommandEval b s₁ .continue s₂) (h₃: CommandEval (.while c b) s₂ .continue s₃): CommandEval (.while c b) s₁ .continue s₃
      | whileFalse {c: Logic} {b: Command} (s: State) (h₁: c.eval s = .false): CommandEval (.while c b) s .continue s

    example (c: Command) (s₁ s₂: State) (r: Result): CommandEval (.seq .break c) s₁ r s₂ := by
      sorry

    example (c: Logic) (b: Command) (s₁ s₂: State) (r: Result): CommandEval (.while c b) s₁ r s₂ := by
      sorry

    example (c: Logic) (b: Command) (s₁ s₂: State) (h₁: c.eval s₁ = true) (h₂: CommandEval b s₁ .break s₂): CommandEval (.while c b) s₁ .continue s₂ := by
      sorry

    example (c₁ c₂: Command) (s₁ s₂ s₃: State) (h₁: CommandEval c₁ s₁ .continue s₂) (h₂: CommandEval c₂ s₂ .continue s₃): CommandEval (.seq c₁ c₂) s₁ .continue s₂ := by
      sorry

    example (c₁ c₂: Command) (s₁ s₂: State) (h₁: CommandEval c₁ s₁ .break s₂): CommandEval (.seq c₁ c₂) s₁ .break s₂ := by
      sorry

    example (c: Logic) (b: Command) (s₁ s₂: State) (h₁: CommandEval (.while c b) s₁ .continue s₂) (h₂: c.eval s₂ = true): ∃ s₃: State, CommandEval b s₃ .break s₂ := by
      sorry

    theorem CommandEval.deterministic (c: Command) (s₁ s₂ s₃: State) (r₁ r₂: Result) (h₁: CommandEval c s₁ r₁ s₂) (h₂: CommandEval c s₁ r₂ s₃): s₂ = s₃ ∧ r₁ = r₂ := by
      sorry
  end BreakImp

  namespace ForImp
    -- TODO
  end ForImp
end SoftwareFoundations.LogicalFoundations.Imp
