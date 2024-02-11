/-
# Working with Structured Data
-/

import SoftwareFoundations.LogicalFoundations.Basics
import SoftwareFoundations.LogicalFoundations.Induction

namespace SoftwareFoundations.LogicalFoundations.Lists
  /-
  ## Pairs of Numbers
  -/

  structure NatProd: Type where
    fst: Nat
    snd: Nat
  deriving Repr

  scoped notation "(‹" fst ", " snd "›)" => NatProd.mk fst snd

  def NatProd.swap: NatProd → NatProd
    | ⟨fst, snd⟩ => ⟨snd, fst⟩

  #check (‹3, 5›)

  #check NatProd.fst
  #check NatProd.snd

  example: (‹3, 5›).fst = 3 := rfl

  namespace Term
    theorem NatProd.surjective (p: NatProd): p = ⟨p.fst, p.snd⟩ := rfl

    example (p: NatProd): ⟨p.snd, p.fst⟩ = p.swap := rfl
    example (p: NatProd): p.swap.fst = p.snd := rfl
  end Term

  namespace Tactic
    theorem NatProd.surjective (p: NatProd): p = ⟨p.fst, p.snd⟩ := by rfl

    example (p: NatProd): ⟨p.snd, p.fst⟩ = p.swap := by rfl
    example (p: NatProd): p.swap.fst = p.snd := by rfl
  end Tactic

  namespace Blended
    theorem NatProd.surjective (p: NatProd): p = ⟨p.fst, p.snd⟩ := rfl

    example (p: NatProd): ⟨p.snd, p.fst⟩ = p.swap := rfl
    example (p: NatProd): p.swap.fst = p.snd := rfl
  end Blended

  /-
  ## Lists of Numbers
  -/

  inductive NatList: Type where
    | nil: NatList
    | cons (hd: Nat) (tl: NatList): NatList
  deriving Repr, BEq

  scoped syntax "[‹" term,* "›]" : term
  scoped syntax:70 term:71 ":::" term:70 : term

  macro_rules
    | `([‹ $hd:term , $tl:term,* ›]) => `(NatList.cons $(Lean.quote hd) [‹ $tl,* ›])
    | `([‹ $hd:term ›])              => `(NatList.cons $(Lean.quote hd) .nil)
    | `([‹ ›])                       => `(NatList.nil)
    | `($hd ::: $tl)                 => `(NatList.cons $(Lean.quote hd) $(Lean.quote tl))

  section
    example: [‹›] = NatList.nil := rfl
    example: [‹1›] = NatList.cons 1 .nil := rfl
    example: [‹1, 2›] = NatList.cons 1 (.cons 2 .nil) := rfl
    example: [‹1, 2, 3›] = NatList.cons 1 (.cons 2 (.cons 3 .nil)) := rfl

    example: 1 ::: [‹›] = NatList.cons 1 .nil := rfl
    example: 1 ::: 2 ::: [‹›] = NatList.cons 1 (.cons 2 .nil) := rfl
    example: 1 ::: 2 ::: 3 ::: [‹›] = NatList.cons 1 (.cons 2 (.cons 3 .nil)) := rfl

    example: 1 ::: [‹2, 3›] = NatList.cons 1 (.cons 2 (.cons 3 .nil)) := rfl
  end

  /-
  ### Repeat
  -/

  @[reducible]
  def NatList.repeat (elem: Nat): Nat → NatList
    | .zero => [‹›]
    | .succ n => elem ::: NatList.repeat elem n

  /-
  ### Length
  -/

  @[reducible]
  def NatList.length: NatList → Nat
    | [‹›] => 0
    | _ ::: tl => 1 + tl.length

  /-
  ### Append
  -/

  @[reducible]
  def NatList.append: NatList → NatList → NatList
    | [‹›], l₂ => l₂
    | hd ::: tl, l₂ => hd ::: (tl.append l₂)

  instance: Append NatList where
    append := NatList.append

  section
    example: [‹1, 2, 3›] ++ [‹4, 5›] = [‹1, 2, 3, 4, 5›] := rfl
    example: [‹›] ++ [‹4, 5›] = [‹4, 5›] := rfl
    example: [‹1, 2, 3›] ++ [‹›] = [‹1, 2, 3›] := rfl
  end

  /-
  ### Head and Tail
  -/

  @[reducible]
  def NatList.hd (default: Nat): NatList → Nat
    | [‹›] => default
    | hd ::: _ => hd

  @[reducible]
  def NatList.tl: NatList → NatList
    | [‹›] => [‹›]
    | _ ::: tl => tl

  section
    example: [‹1, 2, 3›].hd 0 = 1 := rfl
    example: [‹›].hd 0 = 0 := rfl
    example: [‹1, 2, 3›].tl = [‹2, 3›] := rfl
  end

  /-
  ### Examples
  -/

  @[reducible]
  def NatList.nonZero: NatList → NatList
    | [‹›] => [‹›]
    | hd ::: tl => if hd = 0 then tl.nonZero else hd ::: tl.nonZero

  @[reducible]
  def NatList.odd: NatList → NatList
    | [‹›] => [‹›]
    | hd ::: tl => if hd % 2 = 0 then tl.odd else hd ::: tl.odd

  @[reducible]
  def NatList.oddLength (l: NatList): Nat := l.odd.length

  @[reducible]
  def NatList.alternate: NatList → NatList → NatList
    | [‹›], l₂ => l₂
    | l₁, [‹›] => l₁
    | hd₁ ::: tl₁, hd₂ ::: tl₂ => hd₁ ::: hd₂ ::: alternate tl₁ tl₂

  section
    example: [‹0, 1, 0, 2, 3, 0, 0›].nonZero = [‹1, 2, 3›] := rfl

    example: [‹0, 1, 0, 2, 3, 0, 0›].odd = [‹1, 3›] := rfl

    example: [‹1, 0, 3, 1, 4, 5›].oddLength = 4 := rfl
    example: [‹0, 2, 4›].oddLength = 0 := rfl
    example: [‹›].oddLength = 0 := rfl

    example: [‹1, 2, 3›].alternate [‹4, 5, 6›] = [‹1, 4, 2, 5, 3, 6›] := rfl
    example: [‹1›].alternate [‹4, 5, 6›] = [‹1, 4, 5, 6›] := rfl
    example: [‹1, 2, 3›].alternate [‹4›] = [‹1, 4, 2, 3›] := rfl
    example: [‹›].alternate [‹20, 30›] = [‹20, 30›] := rfl
  end

  /-
  ### Bags via Lists
  -/

  abbrev Bag: Type := NatList

  @[reducible]
  def Bag.count (n: Nat): Bag → Nat
    | [‹›] => 0
    | hd ::: tl =>
      if hd = n
      then 1 + count n tl
      else count n tl

  @[reducible]
  def Bag.sum (b₁ b₂: Bag): Bag := b₁ ++ b₂

  @[reducible]
  def Bag.add (n: Nat) (b: Bag): Bag := n ::: b

  @[reducible]
  def Bag.mem (n: Nat): Bag → Bool
    | [‹›] => false
    | hd ::: tl =>
      if hd = n
      then true
      else mem n tl

  @[reducible]
  def Bag.removeFirst (n: Nat): Bag → Bag
    | [‹›] => [‹›]
    | hd ::: tl =>
      if hd = n
      then tl
      else hd ::: removeFirst n tl

  @[reducible]
  def Bag.removeAll (n: Nat): Bag → Bag
    | [‹›] => [‹›]
    | hd ::: tl =>
      if hd = n
      then removeAll n tl
      else hd ::: removeAll n tl

  @[reducible]
  def Bag.included: Bag → Bag → Bool
    | [‹›], _ => true
    | hd ::: tl, l₂ =>
      if aux hd l₂
      then
        let l₂ := Bag.removeFirst hd l₂
        included tl l₂
      else false
    where aux (n: Nat): Bag → Bool
      | [‹›] => false
      | hd ::: tl =>
        if hd = n
        then true
        else aux n tl

  section
    example: Bag.count 1 [‹1, 2, 3, 1, 4, 1›] = 3 := rfl
    example: Bag.count 6 [‹1, 2, 3, 1, 4, 1›] = 0 := rfl

    example: Bag.count 1 (Bag.sum [‹1, 2, 3›] [‹1, 4, 1›]) = 3 := rfl

    example: Bag.count 1 (Bag.add 1 [‹1, 4, 1›]) = 3 := rfl
    example: Bag.count 5 (Bag.add 1 [‹1, 4, 1›]) = 0 := rfl

    example: Bag.mem 1 [‹1, 4, 1›] = true := rfl
    example: Bag.mem 2 [‹1, 4, 1›] = false := rfl

    example: Bag.count 5 (Bag.removeFirst 5 [‹2, 1, 5, 4, 1›]) = 0 := rfl
    example: Bag.count 5 (Bag.removeFirst 5 [‹2, 1, 4, 1›]) = 0 := rfl
    example: Bag.count 4 (Bag.removeFirst 5 [‹2, 1, 4, 5, 1, 4›]) = 2 := rfl
    example: Bag.count 5 (Bag.removeFirst 5 [‹2, 1, 5, 4, 5, 1, 4›]) = 1 := rfl

    example: Bag.count 5 (Bag.removeAll 5 [‹2, 1, 5, 4, 1›]) = 0 := rfl
    example: Bag.count 5 (Bag.removeAll 5 [‹2, 1, 4, 1›]) = 0 := rfl
    example: Bag.count 4 (Bag.removeAll 5 [‹2, 1, 4, 5, 1, 4›]) = 2 := rfl
    example: Bag.count 5 (Bag.removeAll 5 [‹2, 1, 5, 4, 5, 1, 4›]) = 0 := rfl

    example: Bag.included [‹1, 2›] [‹2, 1, 4, 1›] = true := rfl
    example: Bag.included [‹1, 2, 2›] [‹2, 1, 4, 1›] = false := rfl
  end

  namespace Term
    /-
    TODO: Remove Tactic Block
    -/
    theorem Bag.add.inc_count {n: Nat} (b: Bag): Bag.count n (Bag.add n b) = (Bag.count n b).succ :=
      calc Bag.count n (Bag.add n b)
        _ = Bag.count n (n ::: b)                                := rfl
        _ = if n = n then 1 + (Bag.count n b) else Bag.count n b := rfl
        _ = if true then 1 + (Bag.count n b) else Bag.count n b  := by simp
        _ = 1 + (Bag.count n b)                                  := rfl
        _ = (Bag.count n b) + 1                                  := Nat.add_comm 1 (Bag.count n b)
  end Term

  namespace Tactic
    open Basics.Tactic

    theorem Bag.add.inc_count {n: Nat} (b: Bag): Bag.count n (Bag.add n b) = (Bag.count n b).succ := by
      simp [Bag.count]
      rw [Nat.add_comm]
  end Tactic

  namespace Blended
    theorem Bag.add.inc_count {n: Nat} (b: Bag): Bag.count n (Bag.add n b) = (Bag.count n b).succ :=
      calc Bag.count n (Bag.add n b)
        _ = Bag.count n (n ::: b) := by rfl
        _ = 1 + (Bag.count n b)   := by simp [Bag.count]
        _ = (Bag.count n b).succ  := by rw [Nat.add_comm]
  end Blended

  /-
  ## Reasoning About Lists
  -/

  namespace Term
    theorem NatList.nil_append (l: NatList): [‹›] ++ l = l := rfl

    theorem NatList.tl.pred_length: ∀ l: NatList, l.length.pred = l.tl.length
      | [‹›] => rfl
      | hd ::: tl =>
        calc (hd ::: tl).length.pred
          _ = (1 + tl.length).pred        := rfl
          _ = ((0).succ + tl.length).pred := rfl
          _ = (0 + tl.length).succ.pred   := congrArg Nat.pred (Nat.succ_add 0 tl.length)
          _ = tl.length.succ.pred         := congrArg (Nat.pred ∘ Nat.succ) (Nat.zero_add tl.length)
          _ = tl.length                   := Nat.pred_succ tl.length
  end Term

  namespace Tactic
    @[scoped simp]
    theorem NatList.nil_append (l: NatList): [‹›] ++ l = l := by rfl

    theorem NatList.tl.pred_length (l: NatList): l.length.pred = l.tl.length := by
      cases l with
        | nil => rfl
        | cons hd tl => simp [Nat.succ_add, Nat.zero_add, Nat.pred_succ]
  end Tactic

  namespace Blended
    @[scoped simp]
    theorem NatList.nil_append (l: NatList): [‹›] ++ l = l := rfl

    theorem NatList.tl.pred_length: ∀ l: NatList, l.length.pred = l.tl.length
      | [‹›] => rfl
      | hd ::: tl =>
        calc (hd ::: tl).length.pred
          _ = (1 + tl.length).pred      := by rfl
          _ = (0 + tl.length).succ.pred := by rw [Nat.succ_add]
          _ = tl.length                 := by simp [Nat.zero_add, Nat.pred_succ]
  end Blended

  /-
  ### Induction on Lists
  -/

  @[reducible]
  def NatList.rev: NatList → NatList
    | [‹›] => [‹›]
    | hd ::: tl => tl.rev ++ [‹hd›]

  section
    example: [‹1, 2, 3›].rev = [‹3, 2, 1›] := rfl
    example: [‹›].rev = [‹›] := rfl
  end

  namespace Term
    theorem NatList.append_assoc: ∀ l₁ l₂ l₃: NatList, l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃
      | [‹›], l₂, l₃ =>
        calc [‹›] ++ (l₂ ++ l₃)
          _ = l₂ ++ l₃           := NatList.nil_append (l₂ ++ l₃)
          _ = ([‹›] ++ l₂) ++ l₃ := congrArg (·  ++ l₃) (Eq.symm (NatList.nil_append l₂))
      | hd ::: tl, l₂, l₃ =>
        have ih := append_assoc tl l₂ l₃
        calc (hd ::: tl) ++ (l₂ ++ l₃)
          _ = hd ::: tl ++ (l₂ ++ l₃)   := rfl
          _ = hd ::: (tl ++ l₂) ++ l₃   := congrArg (hd ::: .) ih
          _ = ((hd ::: tl) ++ l₂) ++ l₃ := rfl

    theorem NatList.append_length: ∀ l₁ l₂: NatList, (l₁ ++ l₂).length = l₁.length + l₂.length
      | [‹›], l₂ =>
        calc ([‹›] ++ l₂).length
          _ = l₂.length     := congrArg NatList.length (NatList.nil_append l₂)
          _ = 0 + l₂.length := Eq.symm (Nat.zero_add l₂.length)
      | hd ::: tl, l₂ =>
        have ih := append_length tl l₂
        calc ((hd ::: tl) ++ l₂).length
          _ = (hd ::: (tl ++ l₂)).length     := rfl
          _ = 1 + (tl ++ l₂).length          := rfl
          _ = 1 + (tl.length + l₂.length)    := congrArg (1 + ·) ih
          _ = 1 + tl.length + l₂.length      := Eq.symm (Nat.add_assoc 1 tl.length l₂.length)
          _ = (hd ::: tl).length + l₂.length := rfl

    theorem NatList.rev_length: ∀ l: NatList, l.rev.length = l.length
      | [‹›] => rfl
      | hd ::: tl =>
        have ih := rev_length tl
        calc (hd ::: tl).rev.length
          _ = (tl.rev ++ [‹hd›]).length := rfl
          _ = tl.rev.length + 1         := NatList.append_length tl.rev [‹hd›]
          _ = tl.length + 1             := congrArg (· + 1) ih
          _ = 1 + tl.length             := Nat.add_comm tl.length 1
          _ = (hd ::: tl).length        := rfl
  end Term

  namespace Tactic
    theorem NatList.append_assoc (l₁ l₂ l₃: NatList): l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃ := by
      induction l₁ with
        | nil => simp
        | cons hd tl ih =>
          calc (hd ::: tl) ++ (l₂ ++ l₃)
            _ = hd ::: (tl ++ (l₂ ++ l₃)) := by rfl
            _ = hd ::: ((tl ++ l₂) ++ l₃) := by rw [ih]

    @[scoped simp]
    theorem NatList.append_length (l₁ l₂: NatList): (l₁ ++ l₂).length = l₁.length + l₂.length := by
      induction l₁ with
        | nil => simp
        | cons hd tl ih =>
          calc ((hd ::: tl) ++ l₂).length
            _ = 1 + (tl ++ l₂).length          := by rfl
            _ = 1 + (tl.length + l₂.length)    := by rw [ih]
            _ = (hd ::: tl).length + l₂.length := by simp [Nat.add_assoc]

    @[scoped simp]
    theorem NatList.rev_length (l: NatList): l.rev.length = l.length := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          simp [NatList.append_length]
          rw [ih]
          simp [Nat.add_comm]
  end Tactic

  namespace Blended
    theorem NatList.append_assoc: ∀ l₁ l₂ l₃: NatList, l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃
      | [‹›], l₂, l₃ => by simp
      | hd ::: tl, l₂, l₃ =>
        have ih := append_assoc tl l₂ l₃
        calc (hd ::: tl) ++ (l₂ ++ l₃)
          _ = hd ::: (tl ++ (l₂ ++ l₃)) := by rfl
          _ = hd ::: ((tl ++ l₂) ++ l₃) := by rw [ih]
          _ = ((hd ::: tl) ++ l₂) ++ l₃ := by rfl

    @[scoped simp]
    theorem NatList.append_length: ∀ l₁ l₂: NatList, (l₁ ++ l₂).length = l₁.length + l₂.length
      | [‹›], l₂ => by simp
      | hd ::: tl, l₂ =>
        have ih := append_length tl l₂
        calc ((hd ::: tl) ++ l₂).length
          _ = 1 + (tl ++ l₂).length          := by rfl
          _ = 1 + (tl.length + l₂.length)    := by rw [ih]
          _ = (hd ::: tl).length + l₂.length := by simp [Nat.add_assoc]

    @[scoped simp]
    theorem NatList.rev_length: ∀ l: NatList, l.rev.length = l.length
      | [‹›] => by rfl
      | hd ::: tl =>
        have ih := rev_length tl
        calc (hd ::: tl).rev.length
          _ = tl.rev.length + 1  := by simp [NatList.append_length]
          _ = tl.length + 1      := by rw [ih]
          _ = (hd ::: tl).length := by simp [Nat.add_comm]
  end Blended

  /-
  #### Search

  Question: Is there a Lean 4 equivalent of `Search`?  I can find Mathlib
  tactics for it, and `library_search` and `suggest`, but is there a top-level
  `#search` or `#find`, similar to `#eval` and `#print`?
  -/

  /-
  ### List Exercises, Part 1
  -/

  namespace Term
    @[scoped simp]
    theorem NatList.append_nil: ∀ l: NatList, l ++ [‹›] = l
      | [‹›] => rfl
      | hd ::: tl =>
        have ih := append_nil tl
        calc (hd ::: tl) ++ [‹›]
          _ = hd ::: (tl ++ [‹›]) := rfl
          _ = hd ::: tl           := congrArg (hd ::: ·) ih

    theorem NatList.rev_append: ∀ l₁ l₂: NatList, (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev
      | [‹›], l₂ =>
        calc ([‹›] ++ l₂).rev
          _ = l₂.rev             := congrArg NatList.rev (NatList.nil_append l₂)
          _ = l₂.rev ++ [‹›]     := Eq.symm (NatList.append_nil l₂.rev)
          _ = l₂.rev ++ [‹›].rev := rfl
      | hd ::: tl, l₂ =>
        have ih := rev_append tl l₂
        calc ((hd ::: tl) ++ l₂).rev
          _ = (tl ++ l₂).rev ++ [‹hd›].rev := rfl
          _ = (l₂.rev ++ tl.rev) ++ [‹hd›] := congrArg (· ++ [‹hd›]) ih
          _ = l₂.rev ++ (tl.rev ++ [‹hd›]) := Eq.symm (NatList.append_assoc l₂.rev tl.rev [‹hd›])
          _ = l₂.rev ++ (hd ::: tl).rev    := rfl

    theorem NatList.rev_involute: ∀ l: NatList, l.rev.rev = l
      | [‹›] => rfl
      | hd ::: tl =>
        have ih := rev_involute tl
        calc (hd ::: tl).rev.rev
          _ = (tl.rev ++ [‹hd›]).rev := rfl
          _ = [‹hd›] ++ tl.rev.rev   := NatList.rev_append tl.rev [‹hd›]
          _ = [‹hd›] ++ tl           := congrArg ([‹hd›] ++ ·) ih
          _ = hd ::: tl              := rfl

    example (l₁ l₂ l₃ l₄: NatList): l₁ ++ (l₂ ++ (l₃ ++ l₄)) = ((l₁ ++ l₂) ++ l₃) ++ l₄ :=
      calc l₁ ++ (l₂ ++ (l₃ ++ l₄))
        _ = (l₁ ++ l₂) ++ (l₃ ++ l₄) := NatList.append_assoc l₁ l₂ (l₃ ++ l₄)
        _ = ((l₁ ++ l₂) ++ l₃) ++ l₄ := NatList.append_assoc (l₁ ++ l₂) l₃ l₄

    example: ∀ l₁ l₂: NatList, (l₁ ++ l₂).nonZero = l₁.nonZero ++ l₂.nonZero
      | [‹›], _ => rfl
      | 0 ::: tl, l₂ =>
        have ih := _example tl l₂
        calc ((0 ::: tl) ++ l₂).nonZero
          _ = (tl ++ l₂).nonZero       := rfl
          _ = tl.nonZero ++ l₂.nonZero := ih
      | (_ + 1) ::: tl, l₂ =>
        have ih := _example tl l₂
        calc (((_ + 1) ::: tl) ++ l₂).nonZero
          _ = (_ + 1) ::: (tl ++ l₂).nonZero         := rfl
          _ = (_ + 1) ::: tl.nonZero ++ l₂.nonZero   := congrArg ((_ + 1) ::: ·) ih
          _ = ((_ + 1) ::: tl).nonZero ++ l₂.nonZero := rfl

      theorem NatList.beq_refl: ∀ l: NatList, l == l
        | [‹›] => rfl
        | hd ::: tl =>
          have ih := beq_refl tl
          calc (hd ::: tl) == (hd ::: tl)
            _ = and (hd == hd) (tl == tl) := rfl
            _ = and true (tl == tl) := congrArg (· && (tl == tl)) (Nat.beq_refl hd)
            _ = (tl == tl) := Bool.true_and (tl == tl)
            _ = true := ih
  end Term

  namespace Tactic
    @[scoped simp]
    theorem NatList.append_nil (l: NatList): l ++ [‹›] = l := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          calc (hd ::: tl) ++ [‹›]
            _ = hd ::: (tl ++ [‹›]) := by rfl
            _ = hd ::: tl           := by rw [ih]

    theorem NatList.rev_append (l₁ l₂: NatList): (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev := by
      induction l₁ with
        | nil => simp
        | cons hd tl ih =>
          calc ((hd ::: tl) ++ l₂).rev
            _ = (tl ++ l₂).rev ++ [‹hd›].rev     := by rfl
            _ = (l₂.rev ++ tl.rev) ++ [‹hd›].rev := by rw [ih]
            _ = l₂.rev ++ (hd ::: tl).rev        := by simp [NatList.append_assoc]

    theorem NatList.rev_involute (l: NatList): l.rev.rev = l := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          simp [NatList.rev_append]
          rw [ih]
          rfl

    example (l₁ l₂ l₃ l₄: NatList): l₁ ++ (l₂ ++ (l₃ ++ l₄)) = ((l₁ ++ l₂) ++ l₃) ++ l₄ := by
      simp [NatList.append_assoc]

    example (l₁ l₂: NatList): (l₁ ++ l₂).nonZero = l₁.nonZero ++ l₂.nonZero := by
      induction l₁ with
        | nil => rfl
        | cons hd tl ih =>
          cases hd with
            | zero =>
              calc ((0 ::: tl) ++ l₂).nonZero
                _ = (tl ++ l₂).nonZero       := by rfl
                _ = tl.nonZero ++ l₂.nonZero := by rw [ih]
            | succ =>
              calc (((_ + 1) ::: tl) ++ l₂).nonZero
                _ = (_ + 1) ::: (tl ++ l₂).nonZero         := by rfl
                _ = (_ + 1) ::: (tl.nonZero ++ l₂.nonZero) := by rw [ih]
                _ = ((_ + 1) ::: tl).nonZero ++ l₂.nonZero := rfl

    theorem NatList.beq_refl (l: NatList): l == l := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          calc (hd ::: tl) == (hd ::: tl)
            _ = and (hd == hd) (tl == tl) := by rfl
            _ = (tl == tl)                := by simp [Nat.beq_refl, Bool.true_and]
            _ = true                      := by rw [ih]
  end Tactic

  namespace Blended
    @[scoped simp]
    theorem NatList.append_nil: ∀ l: NatList, l ++ [‹›] = l
      | [‹›] => by rfl
      | hd ::: tl =>
        have ih := append_nil tl
        calc (hd ::: tl) ++ [‹›]
          _ = hd ::: (tl ++ [‹›]) := by rfl
          _ = hd ::: tl           := by rw [ih]

    theorem NatList.rev_append: ∀ l₁ l₂: NatList, (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev
      | [‹›], l₂ => by simp
      | hd ::: tl, l₂ =>
        have ih := rev_append tl l₂
          calc ((hd ::: tl) ++ l₂).rev
            _ = (tl ++ l₂).rev ++ [‹hd›].rev     := by rfl
            _ = (l₂.rev ++ tl.rev) ++ [‹hd›].rev := by rw [ih]
            _ = l₂.rev ++ (hd ::: tl).rev        := by simp [NatList.append_assoc]

    theorem NatList.rev_involute: ∀ l: NatList, l.rev.rev = l
      | [‹›] => by rfl
      | hd ::: tl =>
        have ih := rev_involute tl
        calc (hd ::: tl).rev.rev
          _ = [‹hd›].rev ++ tl.rev.rev   := by simp [NatList.rev_append]
          _ = [‹hd›].rev ++ tl           := by rw [ih]

    example (l₁ l₂ l₃ l₄: NatList): l₁ ++ (l₂ ++ (l₃ ++ l₄)) = ((l₁ ++ l₂) ++ l₃) ++ l₄ :=
      calc l₁ ++ (l₂ ++ (l₃ ++ l₄))
        _ = (l₁ ++ l₂) ++ (l₃ ++ l₄) := by rw [NatList.append_assoc]
        _ = ((l₁ ++ l₂) ++ l₃) ++ l₄ := by rw [NatList.append_assoc]

    example: ∀ l₁ l₂: NatList, (l₁ ++ l₂).nonZero = l₁.nonZero ++ l₂.nonZero
      | [‹›], _ => by rfl
      | 0 ::: tl, l₂ =>
        have ih := _example tl l₂
        calc ((0 ::: tl) ++ l₂).nonZero
          _ = (tl ++ l₂).nonZero       := by rfl
          _ = tl.nonZero ++ l₂.nonZero := by rw [ih]
      | (_ + 1) ::: tl, l₂ =>
        have ih := _example tl l₂
        calc (((_ + 1) ::: tl) ++ l₂).nonZero
          _ = (_ + 1) ::: (tl ++ l₂).nonZero         := by rfl
          _ = (_ + 1) ::: (tl.nonZero ++ l₂.nonZero) := by rw [ih]
          _ = ((_ + 1) ::: tl).nonZero ++ l₂.nonZero := by rfl

    theorem NatList.beq_refl: ∀ l: NatList, l == l
      | [‹›] => by rfl
      | hd ::: tl =>
        have ih := beq_refl tl
        calc (hd ::: tl) == (hd ::: tl)
          _ = and (hd == hd) (tl == tl) := by rfl
          _ = (tl == tl)                := by simp [Nat.beq_refl, Bool.true_and]
          _ = true                      := by rw [ih]
  end Blended

  /-
  ### List Exercises, Part 2
  -/

  namespace Term
    /-
    TODO: Remove tactic block
    -/
    theorem Nat.lt_succ: ∀ n: Nat, n < n.succ
      | 0 => by constructor
      | _ + 1 => by constructor

    theorem Bag.count_mem_nonzero: ∀ b: Bag, 0 < Bag.count 1 (Bag.add 1 b)
      | [‹›] =>
        calc 0
          _ < 1 := Nat.lt_succ 0
          _ = Bag.count 1 (Bag.add 1 [‹›]) := rfl
      | b =>
        calc 0
          _ < 1 := Nat.lt_succ 0
          _ ≤ Bag.count 1 b + 1         := Nat.le_add_left 1 (Bag.count 1 b)
          _ = 1 + Bag.count 1 b         := Nat.add_comm (Bag.count 1 b) 1
          _ = Bag.count 1 (1 ::: b)     := rfl
          _ = Bag.count 1 (Bag.add 1 b) := rfl

    theorem Bag.remove_le_count: ∀ b: Bag, Bag.count 0 (Bag.removeFirst 0 b) ≤ Bag.count 0 b
      | [‹›] =>
        calc Bag.count 0 (Bag.removeFirst 0 [‹›])
          _ = Bag.count 0 [‹›] := rfl
          _ = 0 := rfl
          _ ≤ 0 := by simp_arith
      | 0 ::: tl =>
        calc Bag.count 0 (Bag.removeFirst 0 (0 ::: tl))
          _ = Bag.count 0 tl := rfl
          _ ≤ Bag.count 0 (0 ::: tl) := sorry -- NatList.tl.pred_length
      | (_ + 1) ::: tl => sorry

    theorem Bag.count_sum: ∀ b₁ b₂: Bag, Bag.count 0 (Bag.sum b₁ b₂) = Bag.count 0 b₁ + Bag.count 0 b₂
      | [‹›], b₂ =>
        calc Bag.count 0 (Bag.sum [‹›] b₂)
          _ = Bag.count 0 ([‹›] ++ b₂)          := rfl
          _ = Bag.count 0 b₂                    := congrArg (Bag.count 0) (NatList.nil_append b₂)
          _ = 0 + Bag.count 0 b₂                := Eq.symm (Nat.zero_add (Bag.count 0 b₂))
          _ = Bag.count 0 [‹›] + Bag.count 0 b₂ := rfl
      | (0 ::: tl), b₂ =>
        have ih := count_sum tl b₂
        calc Bag.count 0 (Bag.sum (0 ::: tl) b₂)
          _ = 1 + Bag.count 0 (tl ++ b₂)              := rfl
          _ = 1 + (Bag.count 0 tl + Bag.count 0 b₂)   := congrArg (1 + ·) ih
          _ = (1 + Bag.count 0 tl) + Bag.count 0 b₂   := Eq.symm (Nat.add_assoc 1 (Bag.count 0 tl) (Bag.count 0 b₂))
          _ = Bag.count 0 (0 ::: tl) + Bag.count 0 b₂ := rfl
      | ((_ + 1) ::: tl), b₂ =>
        have ih := count_sum tl b₂
        calc Bag.count 0 (Bag.sum ((_ + 1) ::: tl) b₂)
          _ = Bag.count 0 (tl ++ b₂)                        := rfl
          _ = Bag.count 0 tl + Bag.count 0 b₂               := ih
          _ = Bag.count 0 ((_ + 1) ::: tl) + Bag.count 0 b₂ := rfl

    theorem involution_injective {f: α → α} {x₁ x₂: α} (h₁: (x: α) → f (f x) = x) (h₂: f x₁ = f x₂): x₁ = x₂ :=
      calc x₁
        _ = f (f x₁) := Eq.symm (h₁ x₁)
        _ = f (f x₂) := congrArg f h₂
        _ = x₂       := h₁ x₂

    theorem NatList.rev_injective (l₁ l₂: NatList) (h: l₁.rev = l₂.rev): l₁ = l₂ :=
      calc l₁
        _ = l₁.rev.rev := Eq.symm (NatList.rev_involute l₁)
        _ = l₂.rev.rev := congrArg NatList.rev h
        _ = l₂         := NatList.rev_involute l₂
  end Term

  namespace Tactic
    theorem Nat.lt_succ: ∀ n: Nat, n < n.succ := by
      intro
        | 0 => constructor
        | _ + 1 => constructor

    theorem Bag.count_mem_nonzero (b: Bag): 0 < Bag.count 1 (Bag.add 1 b) := by
      cases b with
        | nil => simp [Nat.lt_succ]
        | cons hd tl =>
          calc 0
            _ < 1                           := by simp [Nat.lt_succ]
            _ ≤ Bag.count 1 (hd ::: tl) + 1 := by simp [Nat.le_add_left]
            _ = 1 + Bag.count 1 (hd ::: tl) := by simp [Nat.add_comm]

    theorem Bag.remove_le_count: ∀ b: Bag, Bag.count 0 (Bag.removeFirst 0 b) ≤ Bag.count 0 b := sorry

    theorem Bag.count_sum (b₁ b₂: Bag): Bag.count 0 (Bag.sum b₁ b₂) = Bag.count 0 b₁ + Bag.count 0 b₂ := by
      induction b₁ with
        | nil => simp [NatList.nil_append, Nat.zero_add]
        | cons hd tl ih =>
          cases hd with
            | zero =>
              calc Bag.count 0 (Bag.sum (0 ::: tl) b₂)
                _ = 1 + Bag.count 0 (tl ++ b₂)              := by rfl
                _ = 1 + (Bag.count 0 tl + Bag.count 0 b₂)   := by rw [ih]
                _ = (1 + Bag.count 0 tl) + Bag.count 0 b₂   := by simp [Nat.add_assoc]
                _ = Bag.count 0 (0 ::: tl) + Bag.count 0 b₂ := by rfl
            | succ _ =>
              calc Bag.count 0 (Bag.sum ((_ + 1) ::: tl) b₂)
                _ = Bag.count 0 (tl ++ b₂)                        := by rfl
                _ = Bag.count 0 tl + Bag.count 0 b₂               := by rw [ih]
                _ = Bag.count 0 ((_ + 1) ::: tl) + Bag.count 0 b₂ := by rfl

    theorem involution_injective {f: α → α} {x₁ x₂: α} (h₁: (x: α) → f (f x) = x) (h₂: f x₁ = f x₂): x₁ = x₂ := by
      rw [← (h₁ x₁), h₂, h₁]

    theorem NatList.rev_injective (l₁ l₂: NatList) (h: l₁.rev = l₂.rev): l₁ = l₂ := by
      rw [← NatList.rev_involute l₁, h, NatList.rev_involute]
  end Tactic

  namespace Blended
    theorem Nat.lt_succ: ∀ n: Nat, n < n.succ
      | 0 => by constructor
      | _ + 1 => by constructor

    theorem Bag.count_mem_nonzero: ∀ b: Bag, 0 < Bag.count 1 (Bag.add 1 b)
      | [‹›] => by simp [Nat.lt_succ]
      | b =>
        calc 0
          _ < 1                 := by simp [Nat.lt_succ]
          _ ≤ Bag.count 1 b + 1 := by simp [Nat.le_add_left]
          _ = 1 + Bag.count 1 b := by simp [Nat.add_comm]

    theorem Bag.remove_le_count: ∀ b: Bag, Bag.count 0 (Bag.removeFirst 0 b) ≤ Bag.count 0 b := sorry

    theorem Bag.count_sum: ∀ b₁ b₂: Bag, Bag.count 0 (Bag.sum b₁ b₂) = Bag.count 0 b₁ + Bag.count 0 b₂
      | [‹›], b₂ =>
        calc Bag.count 0 (Bag.sum [‹›] b₂)
          _ = Bag.count 0 b₂                    := by simp [NatList.nil_append]
          _ = 0 + Bag.count 0 b₂                := by simp [Nat.zero_add]
          _ = Bag.count 0 [‹›] + Bag.count 0 b₂ := by rfl
      | (0 ::: tl), b₂ =>
        have ih := count_sum tl b₂
        calc Bag.count 0 (Bag.sum (0 ::: tl) b₂)
          _ = 1 + Bag.count 0 (tl ++ b₂)              := by rfl
          _ = 1 + (Bag.count 0 tl + Bag.count 0 b₂)   := by rw [ih]
          _ = (1 + Bag.count 0 tl) + Bag.count 0 b₂   := by simp [Nat.add_assoc]
          _ = Bag.count 0 (0 ::: tl) + Bag.count 0 b₂ := by rfl
      | ((_ + 1) ::: tl), b₂ =>
        have ih := count_sum tl b₂
        calc Bag.count 0 (Bag.sum ((_ + 1) ::: tl) b₂)
          _ = Bag.count 0 (tl ++ b₂)                        := by rfl
          _ = Bag.count 0 tl + Bag.count 0 b₂               := by rw [ih]
          _ = Bag.count 0 ((_ + 1) ::: tl) + Bag.count 0 b₂ := by rfl

    theorem involution_injective {f: α → α} {x₁ x₂: α} (h₁: (x: α) → f (f x) = x) (h₂: f x₁ = f x₂): x₁ = x₂ :=
      calc x₁
        _ = f (f x₁) := by rw [h₁]
        _ = f (f x₂) := by rw [h₂]
        _ = x₂       := by rw [h₁]

    theorem NatList.rev_injective (l₁ l₂: NatList) (h: l₁.rev = l₂.rev): l₁ = l₂ :=
      calc l₁
        _ = l₁.rev.rev := by rw [NatList.rev_involute]
        _ = l₂.rev.rev := by rw [h]
        _ = l₂         := by rw [NatList.rev_involute]
  end Blended

  /-
  ## Options
  -/

  def NatList.nthOr (default: Nat): Nat → NatList → Nat
    | _, [‹›] => default
    | 0, hd ::: _ => hd
    | n + 1, _ ::: tl => tl.nthOr default n

  inductive NatOption: Type where
    | none: NatOption
    | some (n: Nat): NatOption

  @[reducible]
  def NatOption.elim (default: Nat): NatOption → Nat
    | .none => default
    | .some n => n

  @[reducible]
  def NatList.nthOpt: Nat → NatList → NatOption
    | _, [‹›] => .none
    | 0, hd ::: _ => .some hd
    | n + 1, _ ::: tl => tl.nthOpt n

  @[reducible]
  def NatList.hdOpt: NatList → NatOption
    | [‹›] => .none
    | hd ::: _ => .some hd

  section
    example: [‹4, 5, 6, 7›].nthOpt 0 = .some 4 := rfl
    example: [‹4, 5, 6, 7›].nthOpt 3 = .some 7 := rfl
    example: [‹4, 5, 6, 7›].nthOpt 9 = .none := rfl

    example: [‹›].hdOpt = .none := rfl
    example: [‹1›].hdOpt = .some 1 := rfl
    example: [‹5, 6›].hdOpt = .some 5 := rfl
  end

  namespace Term
    theorem Option.elim_hd (_: Nat): ∀ l: NatList, l.hd default = l.hdOpt.elim default
      | [‹›] => rfl
      | _ ::: _ => rfl
  end Term

  namespace Tactic
    theorem Option.elim_hd (_: Nat): ∀ l: NatList, l.hd default = l.hdOpt.elim default := by
      intro
        | .nil => rfl
        | .cons _ _ => rfl
  end Tactic

  namespace Blended
    theorem Option.elim_hd (_: Nat): ∀ l: NatList, l.hd default = l.hdOpt.elim default
      | [‹›] => by rfl
      | _ ::: _ => by rfl
  end Blended

  /-
  ## Partial Maps
  -/

  def Key: Type := Nat
  deriving Repr, BEq

  instance: OfNat Key n where
    ofNat := n

  inductive PartialMap where
    | empty: PartialMap
    | record (k: Key) (v: Nat) (m: PartialMap): PartialMap

  @[reducible]
  def PartialMap.update (m: PartialMap) (k: Key) (v: Nat): PartialMap :=
    .record k v m

  @[reducible]
  def PartialMap.find (k: Key): PartialMap → NatOption
    | empty => .none
    | record k₂ v m =>
      if k₂ == k
      then .some v
      else m.find k

  namespace Term
    theorem Key.refl (k: Key): k == k := Nat.beq_refl k

    theorem PartialMap.update_eq {k: Key} {v: Nat} (m: PartialMap): (m.update k v).find k = .some v :=
      calc (m.update k v).find k
        _ = (PartialMap.record k v m).find k     := rfl
        _ = if k == k then .some v else m.find k := rfl
        _ = if true then .some v else m.find k   := congrArg (if . then .some v else m.find k) (Key.refl k)
        _ = .some v                              := rfl

    theorem PartialMap.update_neq {k₁ k₂: Key} {v: Nat} (h: (k₁ == k₂) = false) (m: PartialMap): (m.update k₁ v).find k₂ = m.find k₂ :=
      calc (m.update k₁ v).find k₂
        _ = (PartialMap.record k₁ v m).find k₂      := rfl
        _ = if k₁ == k₂ then .some v else m.find k₂ := rfl
        _ = if false then .some v else m.find k₂    := congrArg (if · then .some v else m.find k₂) h
        _ = m.find k₂                               := rfl
  end Term

  namespace Tactic
    theorem Key.refl (k: Key): k == k := by apply Nat.beq_refl

    theorem PartialMap.update_eq {k: Key} {v: Nat} (m: PartialMap): (m.update k v).find k = .some v := by
      calc (m.update k v).find k
        _ = if k == k then .some v else m.find k := by rfl
        _ = if true then .some v else m.find k   := by rw [Key.refl]

    theorem PartialMap.update_neq {k₁ k₂: Key} {v: Nat} (h: (k₁ == k₂) = false) (m: PartialMap): (m.update k₁ v).find k₂ = m.find k₂ := by
      calc (m.update k₁ v).find k₂
        _ = if k₁ == k₂ then .some v else m.find k₂ := by rfl
        _ = if false then .some v else m.find k₂    := by rw [h]
  end Tactic

  namespace Blended
    theorem Key.refl (k: Key): k == k := Nat.beq_refl k

    theorem PartialMap.update_eq {k: Key} {v: Nat} (m: PartialMap): (m.update k v).find k = .some v :=
      calc (m.update k v).find k
        _ = if k == k then .some v else m.find k := by rfl
        _ = if true then .some v else m.find k   := by rw [Key.refl]

    theorem PartialMap.update_neq {k₁ k₂: Key} {v: Nat} (h: (k₁ == k₂) = false) (m: PartialMap): (m.update k₁ v).find k₂ = m.find k₂ :=
      calc (m.update k₁ v).find k₂
        _ = if k₁ == k₂ then .some v else m.find k₂ := by rfl
        _ = if false then .some v else m.find k₂    := by rw [h]
  end Blended
end SoftwareFoundations.LogicalFoundations.Lists
