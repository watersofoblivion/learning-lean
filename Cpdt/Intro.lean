/-
# Some Quick Examples
-/

namespace Untyped
  inductive BinOp: Type where
    | plus
    | times

  inductive Expr: Type where
    | const: Nat → Expr
    | binOp: BinOp → Expr → Expr → Expr

  inductive Instr: Type where
    | const: Nat → Instr
    | binOp: BinOp → Instr

  abbrev Program := List Instr
  abbrev Stack := List Nat

  namespace Test
    private def two: Expr := .const 2
    private def seven: Expr := .const 7

    def fourtyTwo: Expr := Expr.const 42
    def twoPlusTwo: Expr := Expr.binOp .plus two two
    def twoPlusTwoTimesSeven: Expr := Expr.binOp .times twoPlusTwo seven
  end Test

  namespace BinOp
    def eval (op: BinOp): Nat → Nat → Nat :=
      match op with
        | plus => Nat.add
        | times => Nat.mul
  end BinOp

  namespace Expr
    def eval: Expr → Nat
      | const n => n
      | binOp op lhs rhs => op.eval lhs.eval rhs.eval

    example: Test.fourtyTwo.eval = 42 := rfl
    example: Test.twoPlusTwo.eval = 4 := rfl
    example: Test.twoPlusTwoTimesSeven.eval = 28 := rfl

    def compile: Expr → Program
      | const n => [Instr.const n]
      | binOp op lhs rhs =>
        let op: Program := [Instr.binOp op]
        rhs.compile ++ lhs.compile ++ op

    example: Test.fourtyTwo.compile = [Instr.const 42] := rfl
    example: Test.twoPlusTwo.compile = [Instr.const 2, .const 2, .binOp .plus] := rfl
    example: Test.twoPlusTwoTimesSeven.compile = [Instr.const 7, .const 2, .const 2, .binOp .plus, .binOp .times] := rfl
  end Expr

  namespace Instr
    def eval: Instr → Stack → Option Stack
      | .const n, s => .some (n :: s)
      | .binOp op, lhs :: rhs :: s => .some (op.eval lhs rhs :: s)
      | _, _ => .none
  end Instr

  namespace Program
    def eval: Program → Stack → Option Stack
      | .nil, s => .some s
      | instr :: prog, s =>
        match instr.eval s with
          | .none => .none
          | .some s => eval prog s

    example: Test.fourtyTwo.compile.eval [] = Option.some [42] := rfl
    example: Test.twoPlusTwo.compile.eval [] = Option.some [4] := rfl
    example: Test.twoPlusTwoTimesSeven.compile.eval [] = Option.some [28] := rfl
  end Program

  attribute [local simp] BinOp.eval Expr.eval Expr.compile Instr.eval Program.eval

  theorem Expr.compile.correct (e: Expr): e.compile.eval [] = Option.some [e.eval] := by
    rw [← List.append_nil (e.compile)]
    rw [correct]
    rfl
  where
    correct (e: Expr) (p: Program) (s: Stack): (e.compile ++ p).eval s = p.eval (e.eval :: s) := by
      induction e with
        | const n => simp
        | binOp op lhs rhs ihₗ ihᵣ =>
          simp [
            List.append_assoc _ (Expr.compile lhs),
            List.append_assoc,
            -Expr.eval
          ]
          sorry
          -- rw [ihᵣ]
end Untyped

namespace Typed
  inductive Ty: Type where
    | bool
    | nat

  inductive BinOp: Ty → Ty → Ty → Type where
    | plus: BinOp .nat .nat .nat
    | times: BinOp .nat .nat .nat
    | eq {ty: Ty}: BinOp ty ty .bool
    | lt: BinOp .nat .nat .bool

  inductive Expr: Ty → Type where
    | constBool: Bool → Expr .bool
    | constNat: Nat → Expr .nat
    | binOp {t₁ t₂ t₃: Ty}: BinOp t₁ t₂ t₃ → Expr t₁ → Expr t₂ → Expr t₃

  abbrev Stack := List Ty

  inductive Instr: Stack → Stack → Type where
    | constBool {s: Stack}: Bool → Instr s (.bool :: s)
    | constNat {s: Stack}: Nat → Instr s (.nat :: s)
    | binOp {t₁ t₂ t₂: Ty} {s: Stack}: BinOp t₁ t₂ t₃ → Instr (t₁ :: t₂ :: s) (t₃ :: s)

  inductive Program: Stack → Stack → Type where
    | nil {s: Stack}: Program s s
    | cons {s₁ s₂ s₃: Stack}: Instr s₁ s₂ → Program s₂ s₃ → Program s₁ s₃

  namespace Test
    private def two: Expr .nat := .constNat 2
    private def seven: Expr .nat := .constNat 7
    private def twoPlusTwo: Expr .nat := .binOp .plus two two

    def fourtyTwo: Expr .nat := Expr.constNat 42
    def tru: Expr .bool := Expr.constBool true
    def twoPlusTwoTimesSeven: Expr .nat := Expr.binOp .times twoPlusTwo seven
    def twoPlusTwoEqSeven: Expr .bool := Expr.binOp .eq twoPlusTwo seven
    def twoPlusTwoLtSeven: Expr .bool := Expr.binOp .lt twoPlusTwo seven
  end Test

  namespace Ty
    @[reducible]
    def eval: Ty → Type
      | bool => Bool
      | nat => Nat
  end Ty

  namespace BinOp
    def eval {t₁ t₂ t₃: Ty} (op: BinOp t₁ t₂ t₃): t₁.eval → t₂.eval → t₃.eval :=
      match op with
        | plus => Nat.add
        | times => Nat.mul
        | @eq .bool => beq
        | @eq .nat => Nat.beq
        | lt => lessThan
      where
        beq: Bool → Bool → Bool
          | .true, .true | .false, .false => true
          | _, _ => false
        lessThan: Nat → Nat → Bool
          | .zero, .succ _ => true
          | _, .zero => false
          | .succ n₁, .succ n₂ => lessThan n₁ n₂
  end BinOp

  namespace Stack
    @[reducible]
    def vars: Stack → Type
      | .nil => Unit
      | .cons t ts => t.eval × vars ts
  end Stack

  namespace Instr
    def eval {s₁ s₂: Stack} (i: Instr s₁ s₂): s₁.vars → s₂.vars :=
      match i with
        | constBool b => fun s => (b, s)
        | constNat n => fun s => (n, s)
        | binOp b => fun (t₁, t₂, s') => (b.eval t₁ t₂, s')
  end Instr

  namespace Program
    def eval {s₁ s₂: Stack} (p: Program s₁ s₂): s₁.vars → s₂.vars :=
      match p with
        | nil => fun s => s
        | cons instr prog => fun s => prog.eval (instr.eval s)

    def append {s₁ s₂ s₃: Stack} (p: Program s₁ s₂): Program s₂ s₃ → Program s₁ s₃ :=
      match p with
        | nil => fun p => p
        | cons instr progr => fun p => .cons instr (append progr p)

    instance {s₁ s₂ s₃: Stack}: HAppend (Program s₁ s₂) (Program s₂ s₃) (Program s₁ s₃) where
      hAppend := append
  end Program

  namespace Expr
    def eval {t: Ty}: Expr t → t.eval
      | constBool b => b
      | constNat n => n
      | binOp op lhs rhs => op.eval lhs.eval rhs.eval

    example: Test.fourtyTwo.eval = (42: Nat) := by rfl
    example: Test.tru.eval = true := rfl
    example: Test.twoPlusTwoTimesSeven.eval = (28: Nat) := rfl
    example: Test.twoPlusTwoEqSeven.eval = false := rfl
    example: Test.twoPlusTwoLtSeven.eval = true := rfl

    /-
    def compile {ty: Ty} (e: Expr ty) (s: Stack): Program s (ty :: s) :=
      match e with
        | constBool b => .cons (.constBool b) .nil
        | constNat n => .cons (.constNat n) .nil
        | binOp op lhs rhs =>
          (rhs.compile []) ++ (lhs.compile []) ++ ((.cons (.binOp op) .nil): Program _ _)

    private def boolStack: Stack := [Ty.bool]
    private def natStack: Stack := [Ty.nat]

    example: (Test.fourtyTwo.compile []).eval () = (((42: Nat), ()) : natStack.vars) := rfl
    example: (Test.tru.compile []).eval () = ((true, ()): ([Ty.bool]: Stack).vars) := rfl
    example: (Test.twoPlusTwoTimesSeven.compile []).eval = ((28, ()): ([Ty.nat]: Stack).vars) := rfl
    example: (Test.twoPlusTwoEqSeven.compile []).eval = ((false, ()): ([Ty.bool]: Stack).vars) := rfl
    example: (Test.twoPlusTwoLtSeven.compile []).eval = ((true, ()): ([Ty.bool]: Stack).vars) := rfl
    -/
  end Expr

  /-
  attribute [local simp] Ty.eval BinOp.eval Stack.vars Instr.eval Program.eval Program.append Expr.eval Expr.compile
  -/

  namespace Expr
    /-
    theorem compile.correct {ty: Ty} (e: Expr ty): (e.compile []).eval () = (e.eval, ()) := by
      sorry
    where
      concat {s₁ s₂ s₃: Stack} (p₁: Program s₁ s₂) (p₂: Program s₂ s₃) (s: s₁.vars): (p₁ ++ p₂).eval s = p₂.eval (p₁.eval s) := by
        sorry
      correct {ty: Ty} (e: Expr ty) (s: Stack) (t: s.vars): (e.compile s).eval t = (e.eval, s) := by
        sorry
    -/
  end Expr
end Typed
