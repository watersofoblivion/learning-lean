/-
# Tutorial World
-/

import «ℕGame».«ℕ»

namespace Term
  /-
  ## The `rfl` tactic
  -/

  example (x q: ℕ): (37: ℕ) * x + q = (37: ℕ) * x + q := rfl

  /-
  ## The `rw` tactic
  -/

  example (x y: ℕ): y = x + (7: ℕ) → (2: ℕ) * y = (2: ℕ) * (x + (7: ℕ))
    | h => congrArg (ℕ.mul 2) h

  /-
  ## Two is the number after the number after zero, proven forward.
  -/

  example: (2: ℕ) = (0: ℕ).succ.succ :=
    calc 2
      _ = (1: ℕ).succ      := twoSuccOfOne
      _ = (0: ℕ).succ.succ := congrArg ℕ.succ oneSuccOf0

  /-
  ## Two is the number after the number after zero, proven backwards.
  -/

  example: (2: ℕ) = (0: ℕ).succ.succ :=
    have h: (0: ℕ).succ = 1 := Eq.symm (oneSuccOf0)
    calc (0: ℕ).succ.succ
      _ = (1: ℕ).succ := congrArg ℕ.succ h
      _ = 2           := Eq.symm (twoSuccOfOne)

  /-
  ## Adding zero
  -/

  example (a b c: ℕ): a + (b + (0: ℕ)) + (c + (0: ℕ)) = a + b + c :=
    have hb: b + 0 = b := addZero b
    have hc: c + 0 = c := addZero c
    have h: a + (b + 0) = a + b := congrArg (ℕ.add a) hb
    have hp: ℕ.add (a + (b + 0)) = ℕ.add (a + b) := congrArg ℕ.add h
    calc a + (b + 0) + (c + 0)
      _ = a + (b + 0) + c := congrArg (ℕ.add (ℕ.add a (b + 0))) hc
      _ = a + b + c       := congrFun hp c

  /-
  ## Precision Rewriting
  -/

  -- Same as "Adding Zero" above

  /-
  ## Add Successor
  -/

  theorem succEqAddOne (n: ℕ): n.succ = n + (1: ℕ) :=
    have h₁: n = n + ℕ.zero := Eq.symm (addZero n)
    have h₂: ℕ.zero.succ = 1 := Eq.symm (oneSuccOfZero)
    calc n.succ
      _ = (n + ℕ.zero).succ := congrArg ℕ.succ h₁
      _ = n + ℕ.zero.succ   := Eq.symm (addSucc n ℕ.zero)
      _ = n + 1             := congrArg (ℕ.add n) h₂

  /-
  ## 2 + 2 = 4
  -/

  example: (2: ℕ) + (2: ℕ) = (4: ℕ) :=
    let add2 := ℕ.add 2
    let succSucc := ℕ.succ ∘ ℕ.succ
    calc (2: ℕ) + 2
      _ = 2 + (1: ℕ).succ        := congrArg add2 twoSuccOfOne
      _ = 2 + ℕ.zero.succ.succ   := congrArg add2 (congrArg ℕ.succ oneSuccOfZero)
      _ = (2 + ℕ.zero.succ).succ := addSucc 2 ℕ.zero.succ
      _ = (2 + ℕ.zero).succ.succ := congrArg ℕ.succ (addSucc 2 ℕ.zero)
      _ = (2: ℕ).succ.succ       := congrArg succSucc (addZero 2)
      _ = (3: ℕ).succ            := congrArg ℕ.succ (Eq.symm threeSuccOfTwo)
      _ = 4                      := Eq.symm fourSuccOfThree
end Term

namespace Tactic
  /-
  ## The `rfl` tactic
  -/

  example (x q: ℕ): (37: ℕ) * x + q = (37: ℕ) * x + q := by
    rfl

  /-
  ## The `rw` tactic
  -/

  example (x y: ℕ) (h: y = x + (7: ℕ)): (2: ℕ) * y = (2: ℕ) * (x + (7: ℕ)) := by
    rw [h]

  /-
  ## Two is the number after the number after zero, proven forward.
  -/

  example: (2: ℕ) = (0: ℕ).succ.succ := by
    rw [twoSuccOfOne, oneSuccOf0]

  /-
  ## Two is the number after the number after zero, proven backwards.
  -/

  example: (2: ℕ) = (0: ℕ).succ.succ := by
    rw [← oneSuccOf0, ← twoSuccOfOne]

  /-
  ## Adding zero
  -/

  example (a b c: ℕ): a + (b + (0: ℕ)) + (c + (0: ℕ)) = a + b + c := by
    repeat rw [add0]

  /-
  ## Precision Rewriting
  -/

  example (a b c: ℕ): a + (b + (0: ℕ)) + (c + (0: ℕ)) = a + b + c := by
    rw [add0 c, add0 b]

  /-
  ## Add Successor
  -/

  theorem succEqAddOne (n: ℕ): n.succ = n + (1: ℕ) := by
    rw [oneSuccOfZero, addSucc, addZero]

  /-
  ## 2 + 2 = 4
  -/

  example: (2: ℕ) + (2: ℕ) = (4: ℕ) := by
    rw [twoSuccOfOne, oneSuccOfZero]
    rw [fourSuccOfThree, threeSuccOfTwo, twoSuccOfOne, oneSuccOfZero]
    repeat rw [addSucc]
    rw [addZero]
end Tactic

namespace Blended
  /-
  ## The `rfl` tactic
  -/

  example (x q: ℕ): (37: ℕ) * x + q = (37: ℕ) * x + q := rfl

  /-
  ## The `rw` tactic
  -/

  example (x y: ℕ): y = x + (7: ℕ) → (2: ℕ) * y = (2: ℕ) * (x + (7: ℕ))
    | h => by rw [h]

  /-
  ## Two is the number after the number after zero, proven forward.
  -/

  example: (2: ℕ) = (0: ℕ).succ.succ :=
    calc 2
      _ = (1: ℕ).succ      := by rw [twoSuccOfOne]
      _ = (0: ℕ).succ.succ := by rw [oneSuccOf0]

  /-
  ## Two is the number after the number after zero, proven backwards.
  -/

  example: (2: ℕ) = (0: ℕ).succ.succ :=
    calc (0: ℕ).succ.succ
      _ = (1: ℕ).succ := by rw [← oneSuccOf0]
      _ = 2           := by rw [← twoSuccOfOne]

  /-
  ## Adding zero
  -/

  example (a b c: ℕ): a + (b + (0: ℕ)) + (c + (0: ℕ)) = a + b + c := by
    calc a + (b + 0) + (c + 0)
      _ = a + b + (c + 0) := by rw [add0]
      _ = a + b + c       := by rw [add0]

  /-
  ## Precision Rewriting
  -/

  -- Same as "Adding Zero" above

  /-
  ## Add Successor
  -/

  theorem succEqAddOne (n: ℕ): n.succ = n + (1: ℕ) := by
    rw [oneSuccOfZero, addSucc, addZero]

  /-
  ## 2 + 2 = 4
  -/

  example: (2: ℕ) + (2: ℕ) = (4: ℕ) :=
    calc 2 + 2
      _ = 2 + ℕ.zero.succ.succ   := by rw [twoSuccOfOne, oneSuccOfZero]
      _ = (2 + ℕ.zero).succ.succ := by repeat rw [addSucc]
      _ = (2: ℕ).succ.succ       := by rw [addZero]
      _ = 4                      := by rw [fourSuccOfThree, threeSuccOfTwo]
end Blended
