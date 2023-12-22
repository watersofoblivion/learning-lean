/-
# Introducing Inductive Types
-/

/-
## Proof Terms
-/

#check (fun n: Nat => n)
#check (fun x: True => x)

#check True.intro
#check (fun _: False => True.intro)
#check (fun x: False => x)

/-
## Enumerations
-/

#check Unit
#check Unit.unit

theorem Unit.singleton: ∀ u: Unit, u = Unit.unit
  | Unit.unit => rfl

#check PUnit.rec
#check PUnit.recOn

theorem False.exFalso: ∀ p: False, 2 + 2 = 5 := by
  intros
  contradiction

#check False.rec
#check False.recOn

theorem Bool.doubleNeg: ∀ b: Bool, (!!b) = b
  | true => rfl
  | false => rfl

#check Bool.rec
#check Bool.recOn

/-
## Simple Recursive Types
-/

def Nat.isZero: Nat → Bool
  | .zero => true
  | _ => false

theorem Nat.leftAdditiveIdentity: ∀ n: Nat, 0 + n = n
  | zero => rfl
  | succ n => congrArg succ (n.leftAdditiveIdentity)

theorem Nat.rightAddititiveIdentity: ∀ n: Nat, n + 0 = n
  | zero => rfl
  | succ n => congrArg succ (n.rightAddititiveIdentity)

#check Nat.rec
#check Nat.recOn

theorem Nat.succInj (n₁ n₂: Nat) (h: n₁.succ = n₂.succ): n₁ = n₂ := by
  injection h

theorem List.appLen: ∀ l₁ l₂: List α, (l₁ ++ l₂).length = l₁.length + l₂.length := by
  intro l₁ l₂
  induction l₁ with
    | nil => sorry
    | cons hd tl ih => sorry
