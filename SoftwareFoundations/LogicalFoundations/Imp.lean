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

    namespace Term
      theorem Arith.optZeroPlus.sound: (a: Arith) → a.optZeroPlus.eval = a.eval
        | .num _ => rfl
        | .plus e₁ e₂ =>
          have ih₁: e₁.optZeroPlus.eval = e₁.eval := sound e₁
          have ih₂: e₂.optZeroPlus.eval = e₂.eval := sound e₂
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
          have ih₁: e₁.optZeroPlus.eval = e₁.eval := sound e₁
          have ih₂: e₂.optZeroPlus.eval = e₂.eval := sound e₂
          calc (Arith.minus e₁ e₂).optZeroPlus.eval
            _ = e₁.optZeroPlus.eval - e₂.optZeroPlus.eval := rfl
            _ = e₁.eval - e₂.eval                         := congr (congrArg Nat.sub ih₁) ih₂
        | .mult e₁ e₂ =>
          have ih₁: e₁.optZeroPlus.eval = e₁.eval := sound e₁
          have ih₂: e₂.optZeroPlus.eval = e₂.eval := sound e₂
          calc (Arith.mult e₁ e₂).optZeroPlus.eval
            _ = e₁.optZeroPlus.eval * e₂.optZeroPlus.eval := rfl
            _ = e₁.eval * e₂.eval                         := congr (congrArg Nat.mul ih₁) ih₂
            _ = (Arith.mult e₁ e₂).eval                   := rfl
    end Term

    namespace Tactic
      theorem Arith.optZeroPlus.sound (a: Arith): a.optZeroPlus.eval = a.eval := by
        induction a with
          | num n => rfl
          | plus e₁ e₂ ih₁ ih₂ =>
            cases e₁ with
              | num n =>
                cases n with
                  | zero => simp_all
                  | succ n =>
                    unfold Arith.optZeroPlus Arith.eval
                    simp_all
              | plus | minus | mult =>
                unfold Arith.optZeroPlus Arith.eval
                simp_all
          | minus _ _ ih₁ ih₂ | mult _ _ ih₁ ih₂ =>
            unfold Arith.optZeroPlus Arith.eval
            simp_all
    end Tactic

    namespace Blended
      theorem Arith.optZeroPlus.sound: (a: Arith) → a.optZeroPlus.eval = a.eval
        | .num _ => by rfl
        | .plus e₁ e₂ =>
          have ih₁: e₁.optZeroPlus.eval = e₁.eval := sound e₁
          have ih₂: e₂.optZeroPlus.eval = e₂.eval := sound e₂
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
          have ih₁: e₁.optZeroPlus.eval = e₁.eval := sound e₁
          have ih₂: e₂.optZeroPlus.eval = e₂.eval := sound e₂
          unfold Arith.eval
          rw [ih₁, ih₂]
    end Blended

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

    namespace Tactic
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
    end Tactic

    namespace Term
      theorem Logic.optZeroPlus.sound: (b: Logic) → b.optZeroPlus.eval = b.eval
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
            _ = (LE.le e₁.eval e₂.eval: Bool)                         := by rw [h₁, h₂] -- TODO: Remove Tactic block.  Currently used for decidability
        | .gt e₁ e₂ =>
          have h₁ := Arith.optZeroPlus.sound e₁
          have h₂ := Arith.optZeroPlus.sound e₂
          calc (Logic.gt e₁ e₂).optZeroPlus.eval
            _ = (GT.gt e₁.optZeroPlus.eval e₂.optZeroPlus.eval: Bool) := rfl
            _ = (GT.gt e₁.eval e₂.eval: Bool)                         := by rw [h₁, h₂] -- TODO: Remove Tactic block.  Currently used for decidability
        | .not b =>
          have ih := sound b
          calc (Logic.not b).optZeroPlus.eval
            _ = not b.optZeroPlus.eval := rfl
            _ = not b.eval             := congrArg not ih
        | .and b₁ b₂ =>
          have ih₁ := sound b₁
          have ih₂ := sound b₂
          calc (Logic.and b₁ b₂).optZeroPlus.eval
            _ = and b₁.optZeroPlus.eval b₂.optZeroPlus.eval := rfl
            _ = and b₁.eval b₂.eval                         := congr (congrArg and ih₁) ih₂
    end Term

    namespace Tactic
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
    end Tactic

    namespace Blended
      theorem Logic.optZeroPlus.sound: (b: Logic) → b.optZeroPlus.eval = b.eval
        | .true | .false => by rfl
        | .eq e₁ e₂ | .neq e₁ e₂ | .le e₁ e₂ | .gt e₁ e₂ => by
          have h₁ := Arith.optZeroPlus.sound e₁
          have h₂ := Arith.optZeroPlus.sound e₂
          unfold Logic.eval
          rw [h₁, h₂]
        | .not b => by
          have ih := sound b
          unfold Logic.eval
          rw [ih]
        | .and b₁ b₂ => by
          have ih₁ := sound b₁
          have ih₂ := sound b₂
          unfold Logic.eval
          rw [ih₁, ih₂]
    end Blended

    /-
    #### MOAR OPTIMIZATION: Constant Folding
    -/

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

    namespace Term
      -- TODO: Remove Tactic Blocks
      theorem Arith.constFold.sound: (e: Arith) → e.constFold.eval = e.eval
        | .num _ => rfl
        | .plus e₁ e₂ =>
          have ih₁ := sound e₁
          have ih₂ := sound e₂
          match h₁: e₁.constFold with
            | .num n₁ =>
              match h₂: e₂.constFold with
                | .num n₂ =>
                  calc (Arith.plus e₁ e₂).constFold.eval
                    _ = (Arith.num (n₁ + n₂)).eval                := by unfold Arith.constFold; rw [h₁, h₂]
                    _ = (Arith.num n₁).eval + (Arith.num n₂).eval := by rfl
                    _ = e₁.constFold.eval + e₂.constFold.eval     := by rw [h₁, h₂]
                    _ = e₁.eval + e₂.eval                         := by rw [ih₁, ih₂]
                | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
            | .plus _ _ | .minus _ _ | .mult _ _ =>
              match h₂: e₂.constFold with
                | .num _ | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
        | .minus e₁ e₂ =>
          have ih₁ := sound e₁
          have ih₂ := sound e₂
          match h₁: e₁.constFold with
            | .num n₁ =>
              match h₂: e₂.constFold with
                | .num n₂ =>
                  calc (Arith.minus e₁ e₂).constFold.eval
                    _ = (Arith.num (n₁ - n₂)).eval                := by unfold Arith.constFold; rw [h₁, h₂]
                    _ = (Arith.num n₁).eval - (Arith.num n₂).eval := by rfl
                    _ = e₁.constFold.eval - e₂.constFold.eval     := by rw [h₁, h₂]
                    _ = e₁.eval - e₂.eval                         := by rw [ih₁, ih₂]
                | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
            | .plus _ _ | .minus _ _ | .mult _ _ =>
              match h₂: e₂.constFold with
                | .num _ | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
        | .mult e₁ e₂ =>
          have ih₁ := sound e₁
          have ih₂ := sound e₂
          match h₁: e₁.constFold with
            | .num n₁ =>
              match h₂: e₂.constFold with
                | .num n₂ =>
                  calc (Arith.mult e₁ e₂).constFold.eval
                    _ = (Arith.num (n₁ * n₂)).eval                := by unfold Arith.constFold; rw [h₁, h₂]
                    _ = (Arith.num n₁).eval * (Arith.num n₂).eval := by rfl
                    _ = e₁.constFold.eval * e₂.constFold.eval     := by rw [h₁, h₂]
                    _ = e₁.eval * e₂.eval                         := by rw [ih₁, ih₂]
                | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
            | .plus _ _ | .minus _ _ | .mult _ _ =>
              match h₂: e₂.constFold with
                | .num _ | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all

      theorem Logic.constFold.sound: (b: Logic) → b.constFold.eval = b.eval := sorry
    end Term

    namespace Tactic
      theorem Arith.constFold.sound (e: Arith): e.constFold.eval = e.eval := by sorry
      theorem Logic.constFold.sound (b: Logic): b.constFold.eval = b.eval := by sorry
    end Tactic

    namespace Blended
      theorem Arith.constFold.sound: (e: Arith) → e.constFold.eval = e.eval
        | .num _ => rfl
        | .plus e₁ e₂ =>
          have ih₁ := sound e₁
          have ih₂ := sound e₂
          match h₁: e₁.constFold with
            | .num n₁ =>
              match h₂: e₂.constFold with
                | .num n₂ =>
                  calc (Arith.plus _ _).constFold.eval
                    _ = (Arith.num (n₁ + n₂)).eval                := by unfold Arith.constFold; rw [h₁, h₂]
                    _ = (Arith.num n₁).eval + (Arith.num n₂).eval := by rfl
                    _ = e₁.constFold.eval + e₂.constFold.eval     := by rw [h₁, h₂]
                    _ = e₁.eval + e₂.eval                         := by rw [ih₁, ih₂]
                | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
            | .plus _ _ | .minus _ _ | .mult _ _ =>
              match e₂.constFold with
                | .num _ | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
        | .minus e₁ e₂ =>
          have ih₁ := sound e₁
          have ih₂ := sound e₂
          match h₁: e₁.constFold with
            | .num n₁ =>
              match h₂: e₂.constFold with
                | .num n₂ =>
                  calc (Arith.minus e₁ e₂).constFold.eval
                    _ = (Arith.num (n₁ - n₂)).eval                := by unfold Arith.constFold; rw [h₁, h₂]
                    _ = (Arith.num n₁).eval - (Arith.num n₂).eval := by rfl
                    _ = e₁.constFold.eval - e₂.constFold.eval     := by rw [h₁, h₂]
                    _ = e₁.eval - e₂.eval                         := by rw [ih₁, ih₂]
                | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
            | .plus _ _ | .minus _ _ | .mult _ _ =>
              match e₂.constFold with
                | .num _ | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
        | .mult e₁ e₂ =>
          have ih₁ := sound e₁
          have ih₂ := sound e₂
          match h₁: e₁.constFold with
            | .num n₁ =>
              match h₂: e₂.constFold with
                | .num n₂ =>
                  calc (Arith.mult e₁ e₂).constFold.eval
                    _ = (Arith.num (n₁ * n₂)).eval                := by unfold Arith.constFold; rw [h₁, h₂]
                    _ = (Arith.num n₁).eval * (Arith.num n₂).eval := by rfl
                    _ = e₁.constFold.eval * e₂.constFold.eval     := by rw [h₁, h₂]
                    _ = e₁.eval * e₂.eval                         := by rw [ih₁, ih₂]
                | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all
            | .plus _ _ | .minus _ _ | .mult _ _ =>
              match e₂.constFold with
                | .num _ | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Arith.constFold Arith.eval
                    simp_all

      theorem Logic.constFold.sound: (b: Logic) → b.constFold.eval = b.eval
        | .true | .false => rfl
        | .eq e₁ e₂ =>
          have ih₁ := Arith.constFold.sound e₁
          have ih₂ := Arith.constFold.sound e₂
          match h₁: e₁.constFold with
            | .num n₁ =>
              match h₂: e₂.constFold with
                | .num n₂ =>
                  if n₁ == n₂
                  then
                    calc (Logic.eq e₁ e₂).constFold.eval
                      _ = (if n₁ == n₂ then Logic.true else Logic.false).eval := by unfold Logic.constFold; rw [h₁, h₂]
                      _ = Logic.true.eval                                     := sorry --
                      _ = BEq.beq (Arith.num n₁).eval (Arith.num n₂).eval     := sorry -- by rfl
                      _ = BEq.beq e₁.constFold.eval e₂.constFold.eval         := by rw [h₁, h₂]
                      _ = BEq.beq e₁.eval e₂.eval                             := by rw [ih₁, ih₂]
                  else
                    calc (Logic.eq e₁ e₂).constFold.eval
                      _ = (if n₁ == n₂ then Logic.true else Logic.false).eval := by unfold Logic.constFold; rw [h₁, h₂]
                      _ = Logic.false.eval                                    := sorry --by unfold Logic.constFold; rw [h₁, h₂]; simp
                      _ = BEq.beq (Arith.num n₁).eval (Arith.num n₂).eval     := sorry -- by rfl
                      _ = BEq.beq e₁.constFold.eval e₂.constFold.eval         := by rw [h₁, h₂]
                      _ = BEq.beq e₁.eval e₂.eval                             := by rw [ih₁, ih₂]
                | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Logic.constFold Logic.eval
                    simp_all
            | .plus _ _ | .minus _ _ | .mult _ _ =>
              match h₂: e₂.constFold with
                | .num _ | .plus _ _ | .minus _ _ | .mult _ _ =>
                  by
                    unfold Logic.constFold Logic.eval
                    simp_all
        | .neq e₁ e₂ => sorry
        | .le e₁ e₂ => sorry
        | .gt e₁ e₂ => sorry
        | .not b => sorry
        | .and b₁ b₂ => sorry
    end Blended

    /-
    ## Defining New Tactics
    -/

    -- TODO: Research defining tactics in Lean

    /-
    ## The `linearith` (`lia`) Tactic
    -/

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

    namespace Term
      theorem Arith.eval_eval {e: Arith} {n: Nat}: ArithEval e n ↔ e.eval = n :=
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

      theorem Logic.eval_eval {l: Logic} {b: Bool}: LogicEval l b ↔ l.eval = b :=
        ⟨mp, mpr⟩
        where
          mp {l: Logic} {b: Bool}: LogicEval l b → l.eval = b
            | .true | .false => rfl
            | .eq _ _ _ _ _ _
            | .neq _ _ _ _ _ _
            | .le _ _ _ _ _ _
            | .gt _ _ _ _ _ _
            | .not _ _ _
            | .and _ _ _ _ _ _ => sorry
          mpr {l: Logic} {b: Bool} (h: l.eval = b): LogicEval l b := sorry
    end Term

    namespace Tactic
      theorem Arith.eval_eval (a: Arith) (n: Nat): ArithEval a n ↔ a.eval = n := by
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

    theorem Logic.eval_eval (l: Logic) (b: Bool): LogicEval l b ↔ l.eval = b := by
      apply Iff.intro
      · intro h
        induction h with
          | true => rfl
          | false => rfl
          | eq e₁ e₂ n₁ n₂ h₁ h₂ =>
            unfold Logic.eval
            rw [Arith.eval_eval] at *
            simp_all
          | neq e₁ e₂ n₁ n₂ h₁ h₂ =>
            unfold Logic.eval
            rw [Arith.eval_eval] at *
            simp_all
          | le e₁ e₂ n₁ n₂ h₁ h₂ =>
            unfold Logic.eval
            rw [Arith.eval_eval] at *
            simp_all
            sorry
          | gt e₁ e₂ n₁ n₂ h₁ h₂ =>
            unfold Logic.eval
            rw [Arith.eval_eval] at *
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
    end Tactic

    namespace Blended
      theorem Arith.eval_eval (a: Arith) (n: Nat): ArithEval a n ↔ a.eval = n := sorry
      theorem Logic.eval_eval (l: Logic) (b: Bool): LogicEval l b ↔ l.eval = b := sorry
    end Blended
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

  declare_syntax_cat state

  syntax ident "=" num : state
  syntax "[State|" state,* "]" : term

  macro_rules
    | `([State| ])                                  => `(State.empty)
    | `([State| $id:ident = $n:num ])               => `(State.empty.update $(Lean.quote (toString id.getId)) $n)
    | `([State| $ss:state,* , $id:ident = $n:num ]) => `([State|$ss,*].update $(Lean.quote (toString id.getId)) $n)

  #check [State| x = 1, y = 2]

  declare_syntax_cat arith

  syntax num : arith
  syntax ident : arith
  syntax:60 arith:60 "+" arith:61 : arith
  syntax:60 arith:60 "-" arith:61 : arith
  syntax:70 arith:70 "*" arith:71 : arith
  syntax "‹num:" term "›" : arith
  syntax "‹id:" term "›" : arith
  syntax "‹" term "›" : arith
  syntax "(" arith ")" : arith

  syntax "[Arith|" arith "]" : term

  macro_rules
    | `([Arith| $n:num])    => `(Arith.num $n)
    | `([Arith| $id:ident]) => `(Arith.ident $(Lean.quote (toString id.getId)))
    | `([Arith| ‹num: $t›]) => `(Arith.num $(Lean.quote t))
    | `([Arith| ‹id: $t›])  => `(Arith.ident $(Lean.quote t))
    | `([Arith| ‹$t›])      => `($(Lean.quote t))
    | `([Arith| $x + $y])   => `(Arith.plus [Arith| $x] [Arith| $y])
    | `([Arith| $x - $y])   => `(Arith.minus [Arith| $x] [Arith| $y])
    | `([Arith| $x * $y])   => `(Arith.mult [Arith| $x] [Arith| $y])
    | `([Arith| ( $e )])    => `([Arith| $e])

  #check [Arith| 42]
  #check [Arith| X]
  #check [Arith| X + Y]
  #check [Arith| X - Y]
  #check [Arith| X * Y]
  #check [Arith| (X + 42) * (19 - Z)]

  private def testNum := 42
  #check [Arith| ‹num: testNum›]

  private def testId := "test-id"
  #check [Arith| ‹id: testId› ]

  declare_syntax_cat logic

  syntax "tru" : logic
  syntax "fls" : logic
  syntax:50 arith "=" arith : logic
  syntax:50 arith "≠" arith : logic
  syntax:50 arith "≤" arith : logic
  syntax:50 arith ">" arith : logic
  syntax:max "!" logic : logic
  syntax:30 logic "&&" logic : logic
  syntax "‹" term "›" : logic
  syntax "(" logic ")" : logic

  syntax "[Logic|" logic "]" : term

  macro_rules
    | `([Logic| tru])                 => `(Logic.true)
    | `([Logic| fls])                 => `(Logic.false)
    | `([Logic| $x:arith = $y:arith]) => `(Logic.eq [Arith| $x] [Arith| $y])
    | `([Logic| $x:arith ≠ $y:arith]) => `(Logic.neq [Arith| $x] [Arith| $y])
    | `([Logic| $x:arith ≤ $y:arith]) => `(Logic.le [Arith| $x] [Arith| $y])
    | `([Logic| $x:arith > $y:arith]) => `(Logic.gt [Arith| $x] [Arith| $y])
    | `([Logic| ! $x])                => `(Logic.not [Logic| $x])
    | `([Logic| $x && $y])            => `(Logic.and [Logic| $x] [Logic| $y])
    | `([Logic| ( $b )])              => `([Logic| $b])
    | `([Logic| ‹$t:term›])           => `($(Lean.quote t))

  #check [Logic| tru]
  #check [Logic| fls]
  #check [Logic| 42 = 69]
  #check [Logic| 42 ≠ 69]
  #check [Logic| 42 ≤ 69]
  #check [Logic| 42 > 69]
  #check [Logic| !(42 = 69)]
  #check [Logic| !(X = 19) && (Y + 99 = 31)]

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

  example: [Arith| 3 + X * 2].eval [State| X = 5] = 13 := rfl
  example: [Arith| z + X * Y].eval [State| X = 5, Y = 4] = 20 := rfl
  example: [Logic| tru && !(X ≤ 4)].eval [State| X = 5] = true := rfl

  /-
  ## Commands
  -/

  inductive Command: Type where
    | skip: Command
    | assign (id: String) (e: Arith): Command
    | seq (c₁ c₂: Command): Command
    | if (c: Logic) (t f: Command): Command
    | while (c: Logic) (b: Command): Command

  declare_syntax_cat cmd

  syntax:50 "skip" : cmd
  syntax:50 ident ":=" arith : cmd
  syntax:50 "‹" term "›" ":=" arith : cmd
  syntax:40 cmd ";" cmd : cmd
  syntax:50 "ite" "(" logic ")" "{" cmd "}" "else" "{" cmd "}" : cmd
  syntax:50 "while" "(" logic ")" "{" cmd "}" : cmd
  syntax "(" cmd ")" : cmd
  syntax "‹" term "›" : cmd

  syntax "[Imp|" cmd "]" : term

  macro_rules
    | `([Imp| skip])                                => `(Command.skip)
    | `([Imp| $id:ident := $e:arith])               => `(Command.assign $(Lean.quote (toString id.getId)) [Arith| $e])
    | `([Imp| ‹$t:term› := $e:arith])               => `(Command.assign $(Lean.quote t) [Arith| $e])
    | `([Imp| $x; $y])                              => `(Command.seq [Imp| $x] [Imp| $y])
    | `([Imp| ite ( $c:logic ) { $t } else { $f }]) => `(Command.if [Logic| $c] [Imp| $t] [Imp| $f])
    | `([Imp| while ( $c:logic ) { $b }])           => `(Command.while [Logic| $c] [Imp| $b])
    | `([Imp| ( $c )])                              => `([Imp| $c])
    | `([Imp| ‹$t:term› ])                          => pure t

  #check [Imp| ite (x ≠ 0) { y := 3; z := 99 } else { z := 42 } ]
  #check [Imp| ‹testId› := 42]

  def factorial := [Imp|
    z := x;
    y := 1;
    while (z ≠ 0) {
      y := y * z;
      z := z - 1
    }
  ]

  #check [Imp| ‹factorial› ]

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

    def plus2 := [Imp| X := X + 2]
    def xTimesYInZ := [Imp| Z := X * Y]

    /- #### Loops -/

    private def subtractSlowlyBody := [Imp|
      Z := Z - 1;
      X := X - 1
    ]

    private def subtractSlowly := [Imp|
      while (X ≠ 0) {
        ‹subtractSlowlyBody›
      }
    ]

    private def subtract3From5Slowly := [Imp|
      X := 3;
      Z := 5;
      ‹subtractSlowly›
    ]

    /- #### An Infinite Loop -/

    def loopForever := [Imp| while (tru) { skip }]
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

  notation:60 s₁ "=[" c "]=>" s₂ => CommandEval c s₁ s₂

  def assignment (id: String) (n: Nat) (s: State): s =[[Imp| ‹id› := ‹num:n›]]=> (s.update id n) :=
      have h: [Arith| ‹num:n›].eval s = n := by
        unfold Arith.eval
        rfl
      CommandEval.assign s h

  section
    /- Useful definitions to save typing -/

    private def x0 := [Imp| X := 0]
    private def x2 := [Imp| X := 2]
    private def y1 := [Imp| Y := 1]
    private def y3 := [Imp| Y := 3]
    private def z2 := [Imp| Z := 2]
    private def z4 := [Imp| Z := 4]

    private def xLe1: Logic := [Logic| X ≤ 1]

    private def branch := [Imp| ite ( ‹xLe1› ) { ‹y3› } else { ‹z4› }]

    def sum := [Imp|
      Y := 0;
      while (X > 0) {
        Y := X + Y;
        X := X - 1
      }
    ]

    /- Example -/

    namespace Term
      example: [State|] =[[Imp| ‹x2›; ‹branch›]]=> [State| X = 2, Z = 4] :=
        let s₁: State := State.empty
        let s₂: State := s₁.update "X" 2
        let s₃: State := s₂.update "Z" 4

        have h₁: s₁ =[x2]=> s₂ := assignment "X" 2 s₁
        have h₂: s₂ =[branch]=> s₃ :=
          have h₁: [Logic| X ≤ 1].eval s₂ = false := by
            unfold Logic.eval
            rfl
          have h₂: s₂ =[z4]=> s₃ := assignment "Z" 4 s₂
          CommandEval.ifFalse s₂ s₃ h₁ h₂

        by
          repeat unfold instCoeListCommand.conv
          exact CommandEval.seq s₁ s₂ s₃ h₁ h₂

      example: [State|] =[[Imp| ‹x0›; ‹y1›; ‹z2›]]=> [State| X = 0, Y = 1, Z = 2] :=
        let s₁: State := State.empty
        let s₂: State := s₁.update "X" 0
        let s₃: State := s₂.update "Y" 1
        let s₄: State := s₃.update "Z" 2

        by
          repeat unfold instCoeListCommand.conv
          sorry

      example: [State| X = 2] =[sum]=> [State| X = 2, Y = 0, Y = 2, X = 1, Y = 3, X = 0] :=
        sorry
    end Term

    namespace Tactic
      example: [State|] =[[Imp| ‹x2›; ‹branch›]]=> [State| X = 2, Z = 4] := by sorry
      example: [State|] =[[Imp| ‹x0›; ‹y1›; ‹z2›]]=> [State| X = 0, Y = 1, Z = 2] := by sorry
      example: [State| X = 2] =[sum]=> [State| X = 2, Y = 0, Y = 2, X = 1, Y = 3, X = 0] := by sorry
    end Tactic

    namespace Blended
      example: [State|] =[[Imp| ‹x2›; ‹branch›]]=> [State| X = 2, Z = 4] := sorry
      example: [State|] =[[Imp| ‹x0›; ‹y1›; ‹z2›]]=> [State| X = 0, Y = 1, Z = 2] := sorry
      example: [State| X = 2] =[sum]=> [State| X = 2, Y = 0, Y = 2, X = 1, Y = 3, X = 0] := sorry
    end Blended
  end

  /-
  ### Determinism of Evaluation
  -/

  namespace Term
    theorem CommandEval.deterministic (c: Command) (s₁ s₂ s₃: State) (h₁: s₁ =[c]=> s₂) (h₂: s₁ =[c]=> s₃): s₂ = s₃ := sorry
  end Term

  namespace Tactic
    theorem CommandEval.deterministic (c: Command) (s₁ s₂ s₃: State) (h₁: s₁ =[c]=> s₂) (h₂: s₁ =[c]=> s₃): s₂ = s₃ := by
      sorry
  end Tactic

  namespace Blended
    theorem CommandEval.deterministic (c: Command) (s₁ s₂ s₃: State) (h₁: s₁ =[c]=> s₂) (h₂: s₁ =[c]=> s₃): s₂ = s₃ := sorry
  end Blended

  /-
  ## Reasoning about Imp Programs
  -/

  namespace Term
    example (s₁ s₂: State) (n: Nat) (h₁: s₁ "X" = n) (h₂: s₁ =[plus2]=> s₂): s₂ "X" = n + 2 := sorry
    example (s₁ s₂: State) (n₁ n₂: Nat) (h₁: s₁ "X" = n₁) (h₂: s₁ "Y" = n₂) (h₃: s₁ =[xTimesYInZ]=> s₂): s₂ "Z" = n₁ * n₂ := sorry
    example (s₁ s₂: State): ¬ s₁ =[loopForever]=> s₂ := sorry
  end Term

  namespace Tactic
    example (s₁ s₂: State) (n: Nat) (h₁: s₁ "X" = n) (h₂: s₁ =[plus2]=> s₂): s₂ "X" = n + 2 := by
      cases h₂ with
        | assign _ h =>
          simp
          repeat unfold Arith.eval at h
          rw [h₁] at h
          apply Eq.symm
          exact h

    example (s₁ s₂: State) (n₁ n₂: Nat) (h₁: s₁ "X" = n₁) (h₂: s₁ "Y" = n₂) (h₃: s₁ =[xTimesYInZ]=> s₂): s₂ "Z" = n₁ * n₂ := by
      cases h₃ with
        | assign _ h =>
          repeat unfold Arith.eval at h
          repeat unfold Arith.eval at h
          rw [h₁, h₂] at h
          simp_all

    example (s₁ s₂: State): ¬ s₁ =[loopForever]=> s₂ := by
      unfold Not
      intro h
      unfold loopForever at h
      cases h with
        | whileTrue h₁ h₂ h₃ => sorry
        | whileFalse h₁ => contradiction
  end Tactic

  namespace Blended
    example (s₁ s₂: State) (n: Nat) (h₁: s₁ "X" = n) (h₂: s₁ =[plus2]=> s₂): s₂ "X" = n + 2 := sorry
    example (s₁ s₂: State) (n₁ n₂: Nat) (h₁: s₁ "X" = n₁) (h₂: s₁ "Y" = n₂) (h₃: s₁ =[xTimesYInZ]=> s₂): s₂ "Z" = n₁ * n₂ := sorry
    example (s₁ s₂: State): ¬ s₁ =[loopForever]=> s₂ := sorry
  end Blended

  def Command.noWhiles: Command → Bool
    | .skip | .assign _ _ | .seq _ _ | .if _ _ _ => true
    | _ => false

  inductive NoWhiles: Command → Prop where
    | skip: NoWhiles .skip
    | assign {id: String} {e: Arith}: NoWhiles (.assign id e)
    | seq {c₁ c₂: Command}: NoWhiles (.seq c₁ c₂)
    | if {c: Logic} {t f: Command}: NoWhiles (.if c t f)

  namespace Term
    theorem NoWhiles.noWhiles (c: Command): c.noWhiles = true ↔ NoWhiles c := sorry
    theorem CommandEval.noWhiles_terminate (s₁ s₂: State) (c: Command) (h: NoWhiles c): s₁ =[c]=> s₂ := sorry
  end Term

  namespace Tactic
    theorem NoWhiles.noWhiles (c: Command): c.noWhiles = true ↔ NoWhiles c := by sorry
    theorem CommandEval.noWhiles_terminate (s₁ s₂: State) (c: Command) (h: NoWhiles c): s₁ =[c]=> s₂ := by sorry
  end Tactic

  namespace Blended
    theorem NoWhiles.noWhiles (c: Command): c.noWhiles = true ↔ NoWhiles c := sorry
    theorem CommandEval.noWhiles_terminate (s₁ s₂: State) (c: Command) (h: NoWhiles c): s₁ =[c]=> s₂ := sorry
  end Blended

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

  declare_syntax_cat asm

  syntax "push" num : asm
  syntax "load" ident : asm
  syntax "plus" : asm
  syntax "minus" : asm
  syntax "mult" : asm

  syntax "[Asm|" asm,* "]" : term

  macro_rules
    | `([Asm| ]) => `([])
    | `([Asm| push $n:num]) => `(StackInstr.push $n :: [])
    | `([Asm| load $id:ident]) => `(StackInstr.load $(Lean.quote (toString id.getId)) :: [])
    | `([Asm| plus]) => `(StackInstr.plus :: [])
    | `([Asm| minus]) => `(StackInstr.minus :: [])
    | `([Asm| mult]) => `(StackInstr.mult :: [])
    | `([Asm| push $n:num , $is:asm,* ]) => `(StackInstr.push $n :: [Asm|$is,*])
    | `([Asm| load $id:ident , $is:asm,* ]) => `(StackInstr.load $(Lean.quote (toString id.getId)) :: [Asm|$is,*])
    | `([Asm| plus , $is:asm,* ]) => `(StackInstr.plus :: [Asm|$is,*])
    | `([Asm| minus , $is:asm,* ]) => `(StackInstr.minus :: [Asm|$is,*])
    | `([Asm| mult , $is:asm,* ]) => `(StackInstr.mult :: [Asm|$is,*])

  #check [Asm|]
  #check [Asm| push 42, load x, plus]

  @[reducible]
  def Program.eval (state: State) (program: Program) (init: Stack): Stack :=
    program.foldl (fun stack instr => instr.eval state stack) init

  example: Program.eval [State|] [Asm| push 5, push 3, push 1, minus] [] = [2, 5] := by rfl
  example: Program.eval [State| X = 3] [Asm| push 4, load X, mult, plus] [3, 4] = [15, 4] := rfl

  @[reducible]
  def Arith.compile: Arith → Program
    | .num n => [.push n]
    | .ident id => [.load id]
    | .plus e₁ e₂ => e₁.compile ++ e₂.compile ++ [.plus]
    | .minus e₁ e₂ => e₁.compile ++ e₂.compile ++ [.minus]
    | .mult e₁ e₂ => e₁.compile ++ e₂.compile ++ [.mult]

  example: [Arith| X - (2 * Y)].compile = [Asm| load X, push 2, load Y, mult, minus] := rfl

  namespace Term
    theorem eval_append (state: State) (p₁ p₂: Program) (stack: Stack): (p₁ ++ p₂).eval state stack = p₂.eval state (p₁.eval state stack) := sorry
    theorem Arith.compile.correct (state: State) (e: Arith): e.compile.eval state Stack.empty = [e.eval state] :=
      sorry
      where
        helper (state: State) (stack: Stack) (e: Arith): e.compile.eval state stack = e.eval state :: stack := sorry
  end Term

  namespace Tactic
    theorem eval_append (state: State) (p₁ p₂: Program) (stack: Stack): (p₁ ++ p₂).eval state stack = p₂.eval state (p₁.eval state stack) := by sorry
    theorem Arith.compile.correct (state: State) (e: Arith): e.compile.eval state Stack.empty = [e.eval state] := by
      sorry
      where
        helper (state: State) (stack: Stack) (e: Arith): e.compile.eval state stack = e.eval state :: stack := by sorry
  end Tactic

  namespace Blended
    theorem eval_append (state: State) (p₁ p₂: Program) (stack: Stack): (p₁ ++ p₂).eval state stack = p₂.eval state (p₁.eval state stack) := sorry
    theorem Arith.compile.correct (state: State) (e: Arith): e.compile.eval state Stack.empty = [e.eval state] :=
      sorry
      where
        helper (state: State) (stack: Stack) (e: Arith): e.compile.eval state stack = e.eval state :: stack := sorry
  end Blended

  @[reducible]
  def Logic.shortCircuitEval (state: State): Logic → Bool
    | .and e₁ e₂ =>
      if e₁.eval state
      then Bool.true
      else e₂.eval state
    | l => l.eval state

  namespace Term
    theorem Logic.shortCircuitEval.sound (state: State) (b: Logic): b.shortCircuitEval state = b.eval state := sorry
  end Term

  namespace Tactic
    theorem Logic.shortCircuitEval.sound (state: State) (b: Logic): b.shortCircuitEval state = b.eval state := by
      induction b
      <;> try rfl
      case and e₁ e₂ h₁ h₂ =>
        sorry
  end Tactic

  namespace Blended
    theorem Logic.shortCircuitEval.sound (state: State) (b: Logic): b.shortCircuitEval state = b.eval state := sorry
  end Blended

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

    declare_syntax_cat break_cmd

    syntax:50 "skip" : break_cmd
    syntax:50 ident ":=" arith : break_cmd
    syntax:50 "‹" term "›" ":=" arith : break_cmd
    syntax:40 break_cmd ";" break_cmd : break_cmd
    syntax:50 "ite" "(" logic ")" "{" break_cmd "}" "else" "{" break_cmd "}" : break_cmd
    syntax:50 "while" "(" logic ")" "{" break_cmd "}" : break_cmd
    syntax:50 "break" : break_cmd
    syntax "(" break_cmd ")" : break_cmd
    syntax "‹" term "›" : break_cmd

    syntax "[Break|" break_cmd "]" : term

    macro_rules
      | `([Break| skip])                                => `(Command.skip)
      | `([Break| $id:ident := $e:arith])               => `(Command.assign $(Lean.quote (toString id.getId)) [Arith| $e])
      | `([Break| ‹$t:term› := $e:arith])           => `(Command.assign $(Lean.quote t) [Arith| $e])
      | `([Break| $x; $y])                              => `(Command.seq [Break| $x] [Break| $y])
      | `([Break| ite ( $c:logic ) { $t } else { $f }]) => `(Command.if [Logic| $c] [Break| $t] [Break| $f])
      | `([Break| while ( $c:logic ) { $b }])           => `(Command.while [Logic| $c] [Break| $b])
      | `([Break| break ])                              => `(Command.break)
      | `([Break| ( $c )])                              => `([Break| $c])
      | `([Break| ‹$t:term› ])                      => pure t

    inductive CommandEval: Command → State → Result → State → Prop where
      | skip (s: State): CommandEval .skip s .continue s
      | break (s: State): CommandEval .break s .break s
      | assign {e: Arith} {n: Nat} {id: String} (s: State) (h: e.eval s = n): CommandEval (.assign id e) s .continue (s.update id n)
      | seq {c₁ c₂: Command} (s₁ s₂ s₃: State) (h₁: CommandEval c₁ s₁ .continue s₂) (h₂: CommandEval c₂ s₂ .continue s₃): CommandEval (.seq c₁ c₂) s₁ .continue s₃
      | ifTrue {c: Logic} {t f: Command} (s₁ s₂: State) (h₁: c.eval s₁ = .true) (h₂: CommandEval t s₁ .continue s₂): CommandEval (.if c t f) s₁ .continue s₂
      | ifFalse {c: Logic} {t f: Command} (s₁ s₂: State) (h₁: c.eval s₁ = .false) (h₂: CommandEval f s₁ .continue s₂): CommandEval (.if c t f) s₁ .continue s₂
      | whileTrue {c: Logic} {b: Command} (s₁ s₂ s₃: State) (h₁: c.eval s₁ = .true) (h₂: CommandEval b s₁ .continue s₂) (h₃: CommandEval (.while c b) s₂ .continue s₃): CommandEval (.while c b) s₁ .continue s₃
      | whileFalse {c: Logic} {b: Command} (s: State) (h₁: c.eval s = .false): CommandEval (.while c b) s .continue s

    notation s₁ "=[" c "]=[" r "]=>" s₂ => CommandEval c s₁ r s₂

    namespace Term
      example (c: Command) (s₁ s₂: State) (r: Result): s₁ =[[Break| break; ‹c›]]=[r]=> s₂ := sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (r: Result): s₁ =[[Break| while (‹c›) { ‹b› }]]=[r]=> s₂ := sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (h₁: c.eval s₁ = true) (h₂: s₁ =[b]=[.break]=> s₂): s₁ =[[Break| while (‹c›) { ‹b› }]]=[.continue]=> s₂ := sorry
      example (c₁ c₂: Command) (s₁ s₂ s₃: State) (h₁: s₁ =[c₁]=[.continue]=> s₂) (h₂: s₂ =[c₂]=[.continue]=> s₃): s₁ =[[Break| ‹c₁›; ‹c₂›]]=[.continue]=> s₂ := sorry
      example (c₁ c₂: Command) (s₁ s₂: State) (h₁: s₁ =[c₁]=[.break]=> s₂): s₁ =[[Break| ‹c₁›; ‹c₂›]]=[.break]=> s₂ := sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (h₁: s₁ =[[Break| while (‹c›) { ‹b› }]]=[.continue]=> s₂) (h₂: c.eval s₂ = true): ∃ s₃: State, s₃ =[b]=[.break]=> s₂ := sorry

      theorem CommandEval.deterministic (c: Command) (s₁ s₂ s₃: State) (r₁ r₂: Result) (h₁: s₁ =[c]=[r₁]=> s₂) (h₂: s₁ =[c]=[r₂]=> s₃): s₂ = s₃ ∧ r₁ = r₂ := sorry
    end Term

    namespace Tactic
      example (c: Command) (s₁ s₂: State) (r: Result): s₁ =[[Break| break; ‹c›]]=[r]=> s₂ := by
        sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (r: Result): s₁ =[[Break| while (‹c›) { ‹b› }]]=[r]=> s₂ := by
        sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (h₁: c.eval s₁ = true) (h₂: s₁ =[b]=[.break]=> s₂): s₁ =[[Break| while (‹c›) { ‹b› }]]=[.continue]=> s₂ := by
        sorry
      example (c₁ c₂: Command) (s₁ s₂ s₃: State) (h₁: s₁ =[c₁]=[.continue]=> s₂) (h₂: s₂ =[c₂]=[.continue]=> s₃): s₁ =[[Break| ‹c₁›; ‹c₂›]]=[.continue]=> s₂ := by
        sorry
      example (c₁ c₂: Command) (s₁ s₂: State) (h₁: s₁ =[c₁]=[.break]=> s₂): s₁ =[[Break| ‹c₁›; ‹c₂›]]=[.break]=> s₂ := by
        sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (h₁: s₁ =[[Break| while (‹c›) { ‹b› }]]=[.continue]=> s₂) (h₂: c.eval s₂ = true): ∃ s₃: State, s₃ =[b]=[.break]=> s₂ := by
        sorry

      theorem CommandEval.deterministic (c: Command) (s₁ s₂ s₃: State) (r₁ r₂: Result) (h₁: s₁ =[c]=[r₁]=> s₂) (h₂: s₁ =[c]=[r₂]=> s₃): s₂ = s₃ ∧ r₁ = r₂ := by
        sorry
    end Tactic

    namespace Blended
      example (c: Command) (s₁ s₂: State) (r: Result): s₁ =[[Break| break; ‹c›]]=[r]=> s₂ := sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (r: Result): s₁ =[[Break| while (‹c›) { ‹b› }]]=[r]=> s₂ := sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (h₁: c.eval s₁ = true) (h₂: s₁ =[b]=[.break]=> s₂): s₁ =[[Break| while (‹c›) { ‹b› }]]=[.continue]=> s₂ := sorry
      example (c₁ c₂: Command) (s₁ s₂ s₃: State) (h₁: s₁ =[c₁]=[.continue]=> s₂) (h₂: s₂ =[c₂]=[.continue]=> s₃): s₁ =[[Break| ‹c₁›; ‹c₂›]]=[.continue]=> s₂ := sorry
      example (c₁ c₂: Command) (s₁ s₂: State) (h₁: s₁ =[c₁]=[.break]=> s₂): s₁ =[[Break| ‹c₁›; ‹c₂›]]=[.break]=> s₂ := sorry
      example (c: Logic) (b: Command) (s₁ s₂: State) (h₁: s₁ =[[Break| while (‹c›) { ‹b› }]]=[.continue]=> s₂) (h₂: c.eval s₂ = true): ∃ s₃: State, s₃ =[b]=[.break]=> s₂ := sorry

      theorem CommandEval.deterministic (c: Command) (s₁ s₂ s₃: State) (r₁ r₂: Result) (h₁: s₁ =[c]=[r₁]=> s₂) (h₂: s₁ =[c]=[r₂]=> s₃): s₂ = s₃ ∧ r₁ = r₂ := sorry
    end Blended
end BreakImp

  namespace ForImp
    -- TODO
  end ForImp
end SoftwareFoundations.LogicalFoundations.Imp
