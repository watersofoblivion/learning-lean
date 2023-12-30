/-
# Tutorial World
-/

import «ℕGame».«ℕ»

/--
## The `rfl` tactic
-/

example (x q: ℕ): 37 * x + q = 37 * x + q := rfl

example (x q: ℕ): 37 * x + q = 37 * x + q := by
  rfl

/--
## The `rw` tactic
-/

example (x y: ℕ): y = x + 7 → 2 * y = 2 * (x + 7)
  | h => congrArg (ℕ.mul 2) h

example (x y: ℕ) (h: y = x + 7): 2 * y = 2 * (x + 7) := by
  rw [h]

/--
## Two is the number after the number after zero, proven forward.
-/

example: 2 = (0: ℕ).succ.succ :=
  calc (2: ℕ)
    _ = (1: ℕ).succ      := ℕ.twoSuccOfOne
    _ = (0: ℕ).succ.succ := congrArg ℕ.succ ℕ.oneSuccOf0

example: 2 = (0: ℕ).succ.succ := by
  rw [ℕ.twoSuccOfOne, ℕ.oneSuccOf0]

/--
## Two is the number after the number after zero, proven backwards.
-/

example: 2 = (0: ℕ).succ.succ :=
  calc (0: ℕ).succ.succ
    _ = (1: ℕ).succ := congrArg ℕ.succ (Eq.symm (ℕ.oneSuccOf0))
    _ = (2: ℕ)      := Eq.symm (ℕ.twoSuccOfOne)

example: 2 = (0: ℕ).succ.succ := by
  rw [← ℕ.oneSuccOf0, ← ℕ.twoSuccOfOne]

/--
## Adding zero
-/

example (a b c: ℕ): a + (b + 0) + (c + 0) = a + b + c :=
  have hb: b + 0 = b := ℕ.addZero b
  have hc: c + 0 = c := ℕ.addZero c
  have h: a + (b + 0) = a + b := congrArg (ℕ.add a) hb
  have hp: ℕ.add (a + (b + 0)) = ℕ.add (a + b) := congrArg ℕ.add h
  calc a + (b + 0) + (c + 0)
    _ = a + (b + 0) + c := congrArg (ℕ.add (ℕ.add a (b + 0))) hc
    _ = a + b + c       := congrFun hp c

example (a b c: ℕ): a + (b + 0) + (c + 0) = a + b + c := by
  repeat rw [ℕ.add0]

/--
## Precision Rewriting
-/

-- example (a b c: ℕ): a + (b + 0) + (c + 0) = a + b + c := sorry

example (a b c: ℕ): a + (b + 0) + (c + 0) = a + b + c := by
  rw [ℕ.add0 c, ℕ.add0 b]

/--
## Add Successor
-/

theorem ℕ.succEqAddOne (n: ℕ): n.succ = n + 1 :=
  calc n.succ
    _ = (n + ℕ.zero).succ := congrArg ℕ.succ (Eq.symm (ℕ.addZero n))
    _ = n + ℕ.zero.succ   := Eq.symm (ℕ.addSucc n ℕ.zero)
    _ = n + 1             := congrArg (ℕ.add n) (Eq.symm (ℕ.oneSuccOfZero))

example (n: ℕ): n.succ = n + 1 := by
  rw [ℕ.oneSuccOfZero, ℕ.addSucc, ℕ.addZero]

/--
## 2 + 2 = 4
-/

example: (2: ℕ) + 2 = 4 :=
  calc (2: ℕ) + 2
    _ = (2: ℕ) + (1: ℕ).succ        := congrArg (ℕ.add 2) ℕ.twoSuccOfOne
    _ = (2: ℕ) + ℕ.zero.succ.succ   := congrArg (ℕ.add 2) (congrArg ℕ.succ ℕ.oneSuccOfZero)
    _ = ((2: ℕ) + ℕ.zero.succ).succ := ℕ.addSucc 2 ℕ.zero.succ
    _ = ((2: ℕ) + ℕ.zero).succ.succ := congrArg ℕ.succ (ℕ.addSucc 2 ℕ.zero)
    _ = (2: ℕ).succ.succ            := congrArg (ℕ.succ ∘ ℕ.succ) (ℕ.addZero 2)
    _ = (3: ℕ).succ                 := congrArg ℕ.succ (Eq.symm ℕ.threeSuccOfTwo)
    _ = (4: ℕ)                      := Eq.symm ℕ.fourSuccOfThree

example: (2: ℕ) + 2 = 4 := by
  rw [ℕ.twoSuccOfOne, ℕ.oneSuccOfZero]
  rw [ℕ.fourSuccOfThree, ℕ.threeSuccOfTwo, ℕ.twoSuccOfOne, ℕ.oneSuccOfZero]
  repeat rw [ℕ.addSucc]
  rw [ℕ.addZero]
