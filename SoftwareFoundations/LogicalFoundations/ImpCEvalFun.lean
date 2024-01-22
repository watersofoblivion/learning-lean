/-
# An Evaluation Function for Imp
-/

import «SoftwareFoundations».«LogicalFoundations».«Maps»
import «SoftwareFoundations».«LogicalFoundations».«Imp»

import Mathlib.Tactic.Relation.Trans

/-
## A Broken Evaluator
-/

def Command.broken (state: State): Command → State
  | .skip => state
  | .assign id e => state.update id (e.eval state)
  | .seq c₁ c₂ =>
    state
      |> c₁.broken
      |> c₂.broken
  | .if c t f =>
    if c.eval state
    then t.broken state
    else f.broken state
  | .while _ _ => state

/-
## A Step-Indexed Evaluator
-/

def Command.eval (state: State): Nat → Command → Option State
  | 0, _ => .none
  | .succ _, .skip => .some state
  | .succ _, .assign id e => .some (state.update id (e.eval state))
  | .succ i, .seq c₁ c₂ =>
    let state := c₁.eval state i
    match state with
      | .none => .none
      | .some state => c₂.eval state i
  | .succ i, .if c t f =>
    if c.eval state
    then t.eval state i
    else f.eval state i
  | .succ i, .while c b =>
    if c.eval state
    then
      match b.eval state i with
        | .none => .none
        | .some state => (Command.while c b).eval state i
    else .some state

def Command.eval_test (state: State) (c: Command): Option (Nat × Nat × Nat) :=
  match c.eval state 100 with
    | .none => .none
    | .some state => .some (state "X", state "Y", state "Z")

example: (Command.seq (.assign "X" 2) (.if (.le "X" 1) (.assign "Y" 3) (.assign "Z" 4))).eval_test State.empty = .some (2, 0, 4) := rfl

-- TODO: Pup

def pEven: Command :=
  (.while (.gt "X" 1)
    (.assign "X" (.minus "X" 2)))

example: pEven.eval_test (State.build [("X", 0)]) = .some (0, 0, 0) := rfl
example: pEven.eval_test (State.build [("X", 1)]) = .some (1, 0, 0) := rfl
example: pEven.eval_test (State.build [("X", 2)]) = .some (0, 0, 0) := rfl
example: pEven.eval_test (State.build [("X", 3)]) = .some (1, 0, 0) := rfl
example: pEven.eval_test (State.build [("X", 42)]) = .some (0, 0, 0) := rfl
example: pEven.eval_test (State.build [("X", 43)]) = .some (1, 0, 0) := rfl
example: pEven.eval_test (State.build [("X", 200)]) = .none := rfl

/-
## Relational vs. Step-Indexed Evaluation
-/

theorem Command.eval.equiv_rel (c: Command) (s₁ s₂: State): (∃ i: Nat, c.eval s₁ i = .some s₂) → CommandEval c s₁ s₂ := by
  sorry

theorem Command.eval.step (c: Command) (s₁ s₂: State) (h: CommandEval c s₁ s₂): ∃ i: Nat, c.eval s₁ i = .some s₂ := by
  sorry
  where
    more (i₁ i₂: Nat) (s₁ s₂: State) (c: Command) (h₁: i₁ ≤ i₂) (h₂: c.eval s₁ i₁ = s₂): c.eval s₁ i₂ = s₂ := by
      sorry

theorem Command.eval.equiv_step (c: Command) (s₁ s₂: State): CommandEval c s₁ s₂ ↔ ∃ i: Nat, c.eval s₁ i = .some s₂ := by
  sorry

/-
## Determinism of Evaluation Again
-/

theorem CommandEval.deterministic.better (c: Command) (s₁ s₂ s₃: State) (h₁: CommandEval c s₁ s₂) (h₂: CommandEval c s₁ s₃): s₂ = s₃ := by
  sorry
