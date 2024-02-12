/-
# Polymorphism and Higher-Order Functions
-/

import SoftwareFoundations.LogicalFoundations.Lists

namespace SoftwareFoundations.LogicalFoundations.Poly
  /-
  ## Polymorphism
  -/

  /-
  ### Polymorphic Lists
  -/

  inductive BoolList: Type where
    | nil: BoolList
    | cons (hd: Bool) (tl: BoolList): BoolList

  inductive List (α: Type): Type where
    | nil: List α
    | cons (hd: α) (tl: List α): List α

  syntax "[‹" term,* "›]" : term
  syntax:70 term:71 ":::" term:70 : term

  macro_rules
    | `([‹ $hd:term , $tl:term,* ›]) => `(List.cons $(Lean.quote hd) [‹ $tl,* ›])
    | `([‹ $hd:term ›])              => `(List.cons $(Lean.quote hd) .nil)
    | `([‹ ›])                       => `(List.nil)
    | `($hd ::: $tl)                 => `(List.cons $(Lean.quote hd) $(Lean.quote tl))

  #check @List
  #check @List.nil
  #check @List.cons
  #check @List.nil Nat
  #check @List.cons Nat 3 (@List.nil Nat)
  #check @List.cons Nat 2 (@List.cons Nat 1 (@List.nil Nat))

  #check [‹›]
  #check [‹3›]
  #check [‹2, 1›]

  def List.explicitRepeat (α: Type) (elem: α): Nat → List α
    | 0     => [‹›]
    | n + 1 => elem ::: (List.explicitRepeat α elem n)

  section
    example: List.explicitRepeat Nat 4 2 = [‹4, 4›] := rfl
    example: List.explicitRepeat Bool false 1 = [‹false›] := rfl
  end

  namespace MumbleGrumble
    inductive Mumble: Type where
      | a: Mumble
      | b (x: Mumble) (y: Nat): Mumble
      | c: Mumble

    inductive Grumble (α: Type): Type where
      | d (m: Mumble): Grumble α
      | e (x: α): Grumble α

    #check Grumble.d (.b .a 5)
    #check @Grumble.d Mumble (.b .a 5)
    #check @Grumble.d Bool (.b .a 5)
    #check @Grumble.e Bool true
    #check @Grumble.e Mumble (.b .c 0)
    #check_failure @Grumble.e Bool (.b .c 0)
    #check Mumble.c
  end MumbleGrumble

  /-
  #### Type Annotation Inference
  -/

  /-
  This doesn't work in Lean :'(

  It can't infer the type of the `elem` argument and results in the following error message:

  ```
  failed to infer binder type
  when the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
  ```

  Even explicitly using `@List.nil _` and `@List.cons _ elem (List.inferred elem n)` doesn't solve the issue.
  -/
  -- def List.inferred α elem: Nat → List α
  --   | 0     => [‹›]
  --   | n + 1 => elem ::: (List.inferred α elem n)

  /-
  #### Type Argument Synthesis
  -/

  /-
  Same error as `List.inferred` above.
  -/
  -- def List.synthesized (α: _) (elem: _): Nat → List α
  --   | 0     => [‹›]
  --   | n + 1 => elem ::: (List.synthesized α elem n)

  section
    private def l₁ := @List.cons Nat 1 (@List.cons Nat 2 (@List.cons Nat 3 (@List.nil Nat)))
    private def l₂ := @List.cons _ 1 (@List.cons _ 2 (@List.cons _ 3 (@List.nil _)))
    private def l₃ := List.cons 1 (List.cons 2 (List.cons 3 List.nil))

    example: l₁ = l₂ := rfl
    example: l₁ = l₃ := rfl
    example: l₂ = l₃ := rfl
  end

  /-
  #### Implicit Arguments
  -/

  @[reducible]
  def List.repeat {α: Type} (elem: α): Nat → List α
    | 0     => [‹›]
    | n + 1 => elem ::: (List.repeat elem n)

  @[reducible]
  def List.append {α: Type}: List α → List α → List α
    | [‹›], l₂ => l₂
    | hd ::: tl, l₂ => hd ::: (List.append tl l₂)

  instance: Append (List α) where
    append := List.append

  @[reducible]
  def List.rev {α: Type}: List α → List α
    | [‹›] => [‹›]
    | hd ::: tl => tl.rev ++ [‹hd›]

  @[reducible]
  def List.length {α: Type}: List α → Nat
    | [‹›] => 0
    | _ ::: tl => 1 + tl.length

  section
    example: [‹1, 2›].rev = [‹2, 1›] := rfl
    example: [‹true›].rev = [‹true›] := rfl
    example: [‹1, 2, 3›].length = 3 := rfl
  end

  inductive ImplicitList {α: Type}: Type where
    | nil: ImplicitList
    | cons (hd: α) (tl: @ImplicitList α): ImplicitList

  section
    def il₁ := ImplicitList.cons 1 (.cons 2 (.cons 3 .nil))
    #check il₁
  end

  /-
  #### Supplying Type Arguments Explicitly
  -/

  section
    private def myList: List Nat := [‹›]
    #check (@List.nil: ∀ α: Type, List α)
    #check (@List.nil Nat: List Nat)
  end

  /-
  #### Exercises
  -/

  namespace Term
    theorem List.nil_append: ∀ l: List α, [‹›] ++ l = l
      | [‹›] => rfl
      | _ ::: _ => rfl

    theorem List.append_nil: ∀ l: List α, l ++ [‹›] = l
      | [‹›] => rfl
      | hd ::: tl =>
        have ih := append_nil tl
        calc (hd ::: tl) ++ [‹›]
          _ = hd ::: tl ++ [‹›] := rfl
          _ = hd ::: tl         := congrArg (hd ::: ·) ih

    theorem List.append_assoc: ∀ l₁ l₂ l₃: List α, l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃
      | [‹›], l₂, l₃ =>
        calc [‹›] ++ (l₂ ++ l₃)
          _ = l₂ ++ l₃           := List.nil_append (l₂ ++ l₃)
          _ = ([‹›] ++ l₂) ++ l₃ := congrArg (· ++ l₃) (Eq.symm (List.nil_append l₂))
      | hd ::: tl, l₂, l₃ =>
        have ih := append_assoc tl l₂ l₃
        calc (hd ::: tl) ++ (l₂ ++ l₃)
          _ = hd ::: tl ++ (l₂ ++ l₃)   := rfl
          _ = hd ::: (tl ++ l₂) ++ l₃   := congrArg (hd ::: ·) ih
          _ = ((hd ::: tl) ++ l₂) ++ l₃ := rfl

    theorem List.append_length: ∀ l₁ l₂: List α, (l₁ ++ l₂).length = l₁.length + l₂.length
      | [‹›], l₂ =>
        calc ([‹›] ++ l₂).length
          _ = l₂.length               := congrArg List.length (List.nil_append l₂)
          _ = 0 + l₂.length           := Eq.symm (Nat.zero_add l₂.length)
          _ = [‹›].length + l₂.length := rfl
      | hd ::: tl, l₂ =>
        have ih := append_length tl l₂
        calc ((hd ::: tl) ++ l₂).length
          _ = (hd ::: tl ++ l₂).length       := rfl
          _ = 1 + (tl ++ l₂).length          := rfl
          _ = 1 + (tl.length + l₂.length)    := congrArg (1 + ·) ih
          _ = (1 + tl.length) + l₂.length    := Eq.symm (Nat.add_assoc 1 tl.length l₂.length)
          _ = (hd ::: tl).length + l₂.length := rfl

    theorem List.rev_append: ∀ l₁ l₂: List α, (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev
      | [‹›], l₂ =>
        calc ([‹›] ++ l₂).rev
          _ = l₂.rev             := congrArg List.rev (List.nil_append l₂)
          _ = l₂.rev ++ [‹›]     := Eq.symm (List.append_nil l₂.rev)
          _ = l₂.rev ++ [‹›].rev := rfl
      | hd ::: tl, l₂ =>
        have ih := rev_append tl l₂
        calc ((hd ::: tl) ++ l₂).rev
          _ = (hd ::: tl ++ l₂).rev        := rfl
          _ = (tl ++ l₂).rev ++ [‹hd›]     := rfl
          _ = (l₂.rev ++ tl.rev) ++ [‹hd›] := congrArg (· ++ [‹hd›]) ih
          _ = l₂.rev ++ (tl.rev ++ [‹hd›]) := Eq.symm (List.append_assoc l₂.rev tl.rev [‹hd›])
          _ = l₂.rev ++ ((hd ::: tl).rev)  := rfl

    theorem List.rev_involute: ∀ l: List α, l.rev.rev = l
      | [‹›] => rfl
      | hd ::: tl =>
        have ih := rev_involute tl
        calc (hd ::: tl).rev.rev
          _ = (tl.rev ++ [‹hd›].rev).rev   := rfl
          _ = [‹hd›].rev.rev ++ tl.rev.rev := List.rev_append tl.rev [‹hd›].rev
          _ = [‹hd›] ++ tl                 := congrArg ([‹hd›] ++ ·) ih
          _ = hd ::: tl                    := rfl
  end Term

  namespace Tactic
    @[scoped simp]
    theorem List.nil_append (l: List α): [‹›] ++ l = l := by
      cases l with
        | nil => rfl
        | cons _ _ => rfl

    @[scoped simp]
    theorem List.append_nil (l: List α): l ++ [‹›] = l := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          calc (hd ::: tl) ++ [‹›]
            _ = hd ::: (tl ++ [‹›]) := by rfl
            _ = hd ::: tl           := by rw [ih]

    theorem List.append_assoc (l₁ l₂ l₃: List α): l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃ := by
      induction l₁ with
        | nil => simp
        | cons hd tl ih =>
          calc (hd ::: tl) ++ (l₂ ++ l₃)
            _ = hd ::: (tl ++ (l₂ ++ l₃)) := by rfl
            _ = hd ::: ((tl ++ l₂) ++ l₃) := by rw [ih]
            _ = ((hd ::: tl) ++ l₂) ++ l₃ := by rfl

    theorem List.append_length (l₁ l₂: List α): (l₁ ++ l₂).length = l₁.length + l₂.length := by
      induction l₁ with
        | nil => simp
        | cons hd tl ih =>
          calc ((hd ::: tl) ++ l₂).length
            _ = 1 + (tl ++ l₂).length          := by rfl
            _ = 1 + (tl.length + l₂.length)    := by rw [ih]
            _ = (hd ::: tl).length + l₂.length := by simp [Nat.add_assoc]

    theorem List.rev_append (l₁ l₂: List α): (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev := by
      induction l₁ with
        | nil => simp
        | cons hd tl ih =>
          calc ((hd ::: tl) ++ l₂).rev
            _ = (tl ++ l₂).rev ++ [‹hd›]     := by rfl
            _ = (l₂.rev ++ tl.rev) ++ [‹hd›] := by rw [ih]
            _ = l₂.rev ++ ((hd ::: tl).rev)  := by simp [List.append_assoc]

    theorem List.rev_involute (l: List α): l.rev.rev = l := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          simp [List.rev_append]
          rw [ih]
          rfl
  end Tactic

  namespace Blended
    @[scoped simp]
    theorem List.nil_append: ∀ l: List α, [‹›] ++ l = l
      | [‹›] => by rfl
      | _ ::: _ => by rfl

    @[scoped simp]
    theorem List.append_nil: ∀ l: List α, l ++ [‹›] = l
      | [‹›] => by rfl
      | hd ::: tl =>
        have ih := append_nil tl
        calc (hd ::: tl) ++ [‹›]
          _ = hd ::: (tl ++ [‹›]) := by rfl
          _ = hd ::: tl           := by rw [ih]

    theorem List.append_assoc: ∀ l₁ l₂ l₃: List α, l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃
      | [‹›], l₂, l₃ => by simp
      | hd ::: tl, l₂, l₃ =>
        have ih := append_assoc tl l₂ l₃
        calc (hd ::: tl) ++ (l₂ ++ l₃)
          _ = hd ::: (tl ++ (l₂ ++ l₃)) := by rfl
          _ = hd ::: ((tl ++ l₂) ++ l₃) := by rw [ih]
          _ = ((hd ::: tl) ++ l₂) ++ l₃ := by rfl

    theorem List.append_length: ∀ l₁ l₂: List α, (l₁ ++ l₂).length = l₁.length + l₂.length
      | [‹›], l₂ => by simp [List.length]
      | hd ::: tl, l₂ =>
        have ih := append_length tl l₂
        calc ((hd ::: tl) ++ l₂).length
          _ = 1 + (tl ++ l₂).length          := by rfl
          _ = 1 + (tl.length + l₂.length)    := by rw [ih]
          _ = (hd ::: tl).length + l₂.length := by simp [Nat.add_assoc]

    theorem List.rev_append: ∀ l₁ l₂: List α, (l₁ ++ l₂).rev = l₂.rev ++ l₁.rev
      | [‹›], l₂ => by simp [List.rev]
      | hd ::: tl, l₂ =>
        have ih := rev_append tl l₂
        calc ((hd ::: tl) ++ l₂).rev
          _ = (tl ++ l₂).rev ++ [‹hd›]     := by rfl
          _ = (l₂.rev ++ tl.rev) ++ [‹hd›] := by rw [ih]
          _ = l₂.rev ++ ((hd ::: tl).rev)  := by simp [List.append_assoc]

    theorem List.rev_involute: ∀ l: List α, l.rev.rev = l
      | [‹›] => by rfl
      | hd ::: tl =>
        have ih := rev_involute tl
        calc (hd ::: tl).rev.rev
          _ = [‹hd›] ++ tl.rev.rev := by simp [List.rev, List.rev_append]
          _ = [‹hd›] ++ tl         := by rw [ih]
          _ = hd ::: tl            := by rfl
  end Blended

  /-
  ### Polymorphic Pairs
  -/

  structure Prod (α β: Type): Type where
    fst: α
    snd: β
  deriving Repr

  notation "(‹" fst ", " snd "›)" => Prod.mk fst snd
  notation fst " ‹×› " snd => (Prod fst snd)

  #check Prod.fst
  #check @Prod.fst
  #check Prod.snd
  #check @Prod.snd

  def List.combine: List α → List β → List (α ‹×› β)
    | [‹›], _ | _, [‹›] => [‹›]
    | hd₁ ::: tl₁, hd₂ ::: tl₂ => (‹hd₁, hd₂›) ::: tl₁.combine tl₂

  def List.split: List (α ‹×› β) → (List α ‹×› List β)
    | [‹›] => (‹[‹›], [‹›]›)
    | (‹hd₁, hd₂›) ::: tl =>
      let (‹tl₁, tl₂›) := tl.split
      (‹hd₁ ::: tl₁, hd₂ ::: tl₂›)

  #check List.combine
  #check @List.combine

  section
    example: [‹1, 2›].combine [‹false, false, true, true›] = [‹(‹1, false›), (‹2, false›)›] := rfl

    example: [‹(‹1, false›), (‹2, false›)›].split = (‹[‹1, 2›], [‹false, false›]›) := rfl
  end

  /-
  ### Polymorphic Options
  -/

  namespace OptionPlayground
    inductive Option (α: Type): Type where
      | none: Option α
      | some (x: α): Option α
    deriving Repr
  end OptionPlayground

  @[reducible]
  def List.nth: List α → Nat → Option α
    | [‹›],     _     => .none
    | hd ::: _, 0     => .some hd
    | _ ::: tl, n + 1 => tl.nth n

  @[reducible]
  def List.hd: List α → Option α
    | [‹›] => .none
    | hd ::: _ => .some hd

  section
    example: [‹4, 5, 6, 7›].nth 0   = .some 4     := rfl
    example: [‹[‹1›], [‹2›]›].nth 1 = .some [‹2›] := rfl
    example: [‹true›].nth 2         = .none       := rfl

    example: [‹1, 2›].hd         = .some 1     := rfl
    example: [‹[‹1›], [‹2›]›].hd = .some [‹1›] := rfl
    example: ([‹›]: List α).hd   = .none       := rfl
  end

  /-
  ## Functions as Data
  -/

  /-
  ### Higher-Order Functions
  -/

  def threeTimes (f: α → α) (x: α): α := f (f (f x))

  section
    example: threeTimes (· - 2) 9 = 3 := rfl
    example: threeTimes Basics.Bool.neg .true = .false := rfl
  end

  /-
  ### Filter
  -/

  def List.filter (f: α → Bool): List α → List α
    | [‹›] => [‹›]
    | hd ::: tl =>
      if f hd
      then hd ::: tl.filter f
      else tl.filter f

  def Nat.even? (n: Nat): Bool := n % 2 = 0
  def List.singleton? (l: List α): Bool := l.length = 1
  def Bag.oddMem (l: List Nat): Nat := l.filter (· % 2 = 1) |>.length

  section
    example: List.filter Nat.even? [‹1, 2, 3, 4›] = [‹2, 4›] := rfl
    example: List.filter List.singleton? [‹[‹1, 2›], [‹3›], [‹4›], [‹5, 6, 7›], [‹›], [‹8›]›] = [‹[‹3›], [‹4›], [‹8›]›] := rfl

    example: Bag.oddMem [‹1, 0, 3, 1, 4, 5›] = 4 := rfl
    example: Bag.oddMem [‹0, 2, 4›] = 0 := rfl
    example: Bag.oddMem [‹›] = 0 := rfl
  end

  /-
  ### Anonymous Functions
  -/

  section
    example: threeTimes (fun n => n * n) 2 = 256 := rfl
    example: threeTimes (λ n => n * n) 2 = 256 := rfl

    example: List.filter (λ x => x % 2 = 0) [‹1, 2, 3, 4›] = [‹2, 4›] := rfl
    example: List.filter (λ l => l.length = 1) [‹[‹1, 2›], [‹3›], [‹4›], [‹5, 6, 7›], [‹›], [‹8›]›] = [‹[‹3›], [‹4›], [‹8›]›] := rfl

    example: List.filter (· % 2 = 0) [‹1, 2, 3, 4›] = [‹2, 4›] := rfl
    example: List.filter (List.length · = 1) [‹[‹1, 2›], [‹3›], [‹4›], [‹5, 6, 7›], [‹›], [‹8›]›] = [‹[‹3›], [‹4›], [‹8›]›] := rfl
  end

  def List.even (l: List Nat): List Nat := l.filter (· % 2 = 0)
  def List.gt (n: Nat) (l: List Nat): List Nat := l.filter (· > n)
  def List.evenGt₇ (l: List Nat) := l.even |>.gt 7

  section
    example: [‹1, 2, 6, 9, 10, 3, 12, 8›].evenGt₇ = [‹10, 12, 8›] := rfl
    example: [‹5, 2, 6, 19, 129›].evenGt₇ = [‹›] := rfl
  end

  def List.partition (p: α → Bool): List α → (List α ‹×› List α)
    | [‹›] => (‹[‹›], [‹›]›)
    | hd ::: tl =>
      let (‹tl₁, tl₂›) := tl.partition p
      if p hd
      then (‹hd ::: tl₁, tl₂›)
      else (‹tl₁, hd ::: tl₂›)

  section
    example: List.partition (· % 2 = 1) [‹1, 2, 3, 4, 5›] = (‹[‹1, 3, 5›], [‹2, 4›]›) := rfl
    example: List.partition (λ _ => false) [‹5, 9, 0›] = (‹[‹›], [‹5, 9, 0›]›) := rfl
  end

  /-
  ### Map
  -/

  def List.map (f: α → β): List α → List β
    | [‹›] => [‹›]
    | hd ::: tl => f hd ::: tl.map f

  def List.flatMap (f: α → List β): List α → List β
    | [‹›] => [‹›]
    | hd ::: tl => f hd ++ tl.flatMap f

  def Option.optMap (f: α → β): Option α → Option β
    | .none => .none
    | .some x => .some (f x)

  section
    example: [‹2, 0, 2›].map (· + 3) = [‹5, 3, 5›] := rfl
    example: [‹2, 1, 2, 5›].map (· % 2 == 1) = [‹false, true, false, true›] := rfl
    example: [‹2, 1, 2, 5›].map (λ n => [‹n % 2 == 0, n % 2 == 1›]) = [‹[‹true, false›], [‹false, true›], [‹true, false›], [‹false, true›]›] := rfl

    example: [‹1, 5, 4›].flatMap (λ n => [‹n, n, n›]) = [‹1, 1, 1, 5, 5, 5, 4, 4, 4›] := rfl
  end

  namespace Term
    theorem List.map_append {f: α → β}: ∀ l₁ l₂: List α, (l₁ ++ l₂).map f = l₁.map f ++ l₂.map f
      | [‹›], _ => rfl
      | hd ::: tl, l₂ =>
        have ih := map_append tl l₂
        calc ((hd ::: tl) ++ l₂).map f
          _ = (hd ::: tl ++ l₂).map f := rfl
          _ = f hd ::: (tl ++ l₂).map f := rfl
          _ = f hd ::: tl.map f ++ l₂.map f := congrArg (f hd ::: .) ih
          _ = (hd ::: tl).map f ++ l₂.map f := rfl

    theorem List.map_rev {f: α → β}: ∀ l: List α, l.rev.map f = (l.map f).rev
      | [‹›] => rfl
      | hd ::: tl =>
        have ih := map_rev tl
        calc (hd ::: tl).rev.map f
          _ = (tl.rev ++ [‹hd›]).map f           := rfl
          _ = tl.rev.map f ++ [‹hd›].rev.map f   := List.map_append tl.rev [‹hd›].rev
          _ = (tl.map f).rev ++ [‹hd›].rev.map f := congrArg (· ++ [‹hd›].rev.map f) ih
          _ = (tl.map f).rev ++ [‹f hd›].rev     := rfl
          _ = ((f hd) ::: (tl.map f)).rev        := Eq.symm (List.rev_append ([‹hd›].map f) (tl.map f))
          _ = ((hd ::: tl).map f).rev            := rfl
  end Term

  namespace Tactic
    theorem List.map_append {f: α → β} (l₁ l₂: List α): (l₁ ++ l₂).map f = l₁.map f ++ l₂.map f := by
      induction l₁ with
        | nil => rfl
        | cons hd tl ih =>
          calc ((hd ::: tl) ++ l₂).map f
            _ = f hd ::: (tl ++ l₂).map f       := by rfl
            _ = f hd ::: (tl.map f ++ l₂.map f) := by rw [ih]
            _ = (hd ::: tl).map f ++ l₂.map f   := by rfl

    theorem List.map_rev {f: α → β} (l: List α): l.rev.map f = (l.map f).rev := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          simp [List.map_append]
          rw [ih]
          rfl
  end Tactic

  namespace Blended
    theorem List.map_append {f: α → β}: ∀ l₁ l₂: List α, (l₁ ++ l₂).map f = l₁.map f ++ l₂.map f
      | [‹›], _ => by rfl
      | hd ::: tl, l₂ =>
        have ih := map_append tl l₂
        calc ((hd ::: tl) ++ l₂).map f
          _ = f hd ::: (tl ++ l₂).map f       := by rfl
          _ = f hd ::: (tl.map f ++ l₂.map f) := by rw [ih]
          _ = (hd ::: tl).map f ++ l₂.map f   := by rfl

    theorem List.map_rev {f: α → β}: ∀ l: List α, l.rev.map f = (l.map f).rev
      | [‹›] => by rfl
      | hd ::: tl =>
        have ih := map_rev tl
        calc (hd ::: tl).rev.map f
          _ = tl.rev.map f ++ [‹hd›].rev.map f   := by simp [List.map_append]
          _ = (tl.map f).rev ++ [‹hd›].rev.map f := by rw [ih]
          _ = (tl.map f).rev ++ [‹f hd›].rev     := by rfl
          _ = ((f hd) ::: (tl.map f)).rev        := by simp [List.rev_append]
          _ = ((hd ::: tl).map f).rev            := by rfl
  end Blended

  /-
  ### Fold
  -/

  def List.fold (f: α → β → β) (acc: β): List α → β
    | [‹›] => acc
    | hd ::: tl => f hd (tl.fold f acc)

  section
    #check List.fold (· && ·)

    example: [‹true, true, false, true›].fold (· && ·) true = false := rfl
    example: [‹1, 2, 3, 4›].fold (· * ·) 1 = 24 := rfl
    example: [‹[‹1›], [‹›], [‹2, 3›], [‹4›]›].fold (· ++ ·) [‹›] = [‹1, 2, 3, 4›] := rfl
  end

  /-
  ### Functions that Construct Functions
  -/

  def const (x: α): Nat → α
    | _ => x

  def constTrue := const true

  section
    example: constTrue 0 = true := rfl
    example: (const 5) 99 = 5 := rfl
  end

  def plus3: Nat → Nat := (· + 3)

  section
    example: plus3 4 = 7 := rfl
    example: threeTimes plus3 0 = 9 := rfl
    example: threeTimes (· + 3) 0 = 9 := rfl
  end

  /-
  ## Additional Exercises
  -/

  @[reducible]
  def List.foldLength (l: List α): Nat :=
    l.fold (λ _ acc => acc + 1) 0

  @[reducible]
  def List.foldMap (f: α → β) (l: List α): List β :=
    l.fold (λ hd acc => f hd ::: acc) [‹›]

  namespace Term
    theorem List.foldLength.correct: ∀ l: List α, l.foldLength = l.length
      | [‹›] => rfl
      | hd ::: tl =>
        let f _ acc := acc + 1
        have ih := correct tl
        calc (hd ::: tl).foldLength
          _ = (hd ::: tl).fold f 0 := rfl
          _ = f hd (tl.fold f 0)   := rfl
          _ = f hd tl.foldLength   := rfl
          _ = f hd tl.length       := congrArg (f hd ·) ih
          _ = tl.length + 1        := rfl
          _ = 1 + tl.length        := Nat.add_comm tl.length 1
          _ = (hd ::: tl).length   := rfl

    theorem List.foldMap.correct {f: α → β}: ∀ l: List α, l.foldMap f = l.map f
      | [‹›] => rfl
      | hd ::: tl =>
        let g hd acc := f hd ::: acc
        have ih := correct tl
        calc (hd ::: tl).foldMap f
          _ = (hd ::: tl).fold g [‹›] := rfl
          _ = g hd (tl.fold g [‹›])   := rfl
          _ = g hd (tl.foldMap f)     := rfl
          _ = g hd (tl.map f)         := congrArg (g hd ·) ih
          _ = f hd ::: tl.map f       := rfl
          _ = (hd ::: tl).map f       := rfl
  end Term

  namespace Tactic
    theorem List.foldLength.correct (l: List α): l.foldLength = l.length := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          unfold List.foldLength List.fold List.length
          simp_all [Nat.add_comm]

    theorem List.foldMap.correct {f: α → β} (l: List α): l.foldMap f = l.map f := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          unfold List.foldMap List.fold
          simp_all
          rfl
  end Tactic

  namespace Blended
    theorem List.foldLength.correct: ∀ l: List α, l.foldLength = l.length
      | [‹›] => rfl
      | hd ::: tl =>
        let f _ acc := acc + 1
        have ih := correct tl
        calc (hd ::: tl).foldLength
          _ = f hd tl.foldLength   := by rfl
          _ = f hd tl.length       := by rw [ih]
          _ = (hd ::: tl).length   := by simp [Nat.add_comm]

    theorem List.foldMap.correct {f: α → β}: ∀ l: List α, l.foldMap f = l.map f
      | [‹›] => rfl
      | hd ::: tl =>
        let g hd acc := f hd ::: acc
        have ih := correct tl
        calc (hd ::: tl).foldMap f
          _ = g hd (tl.foldMap f)     := by rfl
          _ = g hd (tl.map f)         := by rw [ih]
          _ = (hd ::: tl).map f       := by rfl
  end Blended

  def Prod.curry (f: (α ‹×› β) → γ) (x: α) (y: β): γ := f (‹x, y›)
  def Prod.uncurry (f: α → β → γ) (p: (α ‹×› β)): γ := f p.fst p.snd

  section
    example: [‹2, 0, 2›].map (Nat.add 3) = [‹5, 3, 5›] := rfl
  end

  def List.tl: List α → List α
    | [‹›] => [‹›]
    | _ ::: tl => tl

  namespace Term
    theorem Prod.uncurry.curry {f: α → β → γ} {x: α} {y: β}: Prod.curry (Prod.uncurry f) x y = f x y := rfl
    theorem Prod.curry.uncurry {f: (α ‹×› β) → γ} {p: (α ‹×› β)}: Prod.uncurry (Prod.curry f) p = f p := rfl

    theorem List.tl.pred_length: ∀ l: List α, l.length.pred = l.tl.length
      | [‹›] => rfl
      | hd ::: tl =>
        calc (hd ::: tl).length.pred
          _ = (1 + tl.length).pred      := rfl
          _ = (0 + tl.length).succ.pred := congrArg Nat.pred (Nat.succ_add 0 tl.length)
          _ = 0 + tl.length             := Nat.pred_succ (0 + tl.length)
          _ = tl.length                 := Nat.zero_add tl.length

    theorem List.nth.length_none: ∀ n: Nat, ∀ l: List α, l.length = n → l.nth n = .none
      | _, [‹›], _ => rfl
      | 0,     hd ::: tl, h =>
        have hf: 0 ≠ 0 :=
          calc 0
            _ = (hd ::: tl).length := Eq.symm h
            _ = 1 + tl.length      := rfl
            _ = tl.length + 1      := Nat.add_comm 1 tl.length
            _ = tl.length.succ     := Nat.succ_eq_add_one tl.length
            _ ≠ 0                  := Nat.succ_ne_zero tl.length
        nomatch hf
      | n + 1, hd ::: tl, h =>
        have ih :=
          have h: tl.length = n :=
            calc tl.length
              _ = (hd ::: tl).length.pred := Eq.symm (List.tl.pred_length (hd :::tl))
              _ = (n + 1).pred            := congrArg Nat.pred h
          length_none n tl h
        calc (hd ::: tl).nth (n + 1)
          _ = tl.nth n := rfl
          _ = .none := ih
  end Term

  namespace Tactic
    theorem Prod.uncurry.curry {f: α → β → γ} {x: α} {y: β}: Prod.curry (Prod.uncurry f) x y = f x y := by rfl
    theorem Prod.curry.uncurry {f: (α ‹×› β) → γ} {p: (α ‹×› β)}: Prod.uncurry (Prod.curry f) p = f p := by rfl

    theorem List.tl.pred_length (l: List α): l.length.pred = l.tl.length := by
      cases l with
        | nil => rfl
        | cons hd tl =>
          simp [Nat.succ_add, Nat.pred_succ, Nat.zero_add]
          rfl

    theorem List.nth.length_none (n: Nat) (l: List α) (h: l.length = n): l.nth n = .none := by
      induction l with
        | nil => rfl
        | cons hd tl ih =>
          cases n with
            | zero =>
              have: 0 ≠ 0 := sorry
              contradiction
            | succ n =>
              have ih :=
                have h: tl.length = n :=
                  calc tl.length
                    _ = (hd ::: tl).length.pred := Eq.symm (List.tl.pred_length (hd ::: tl))
                    _ = (n + 1).pred            := by rw [h]
                length_none n tl h
              simp [List.nth, ih]
  end Tactic

  namespace Blended
    theorem Prod.uncurry.curry {f: α → β → γ} {x: α} {y: β}: Prod.curry (Prod.uncurry f) x y = f x y := rfl
    theorem Prod.curry.uncurry {f: (α ‹×› β) → γ} {p: (α ‹×› β)}: Prod.uncurry (Prod.curry f) p = f p := rfl

    theorem List.tl.pred_length: ∀ l: List α, l.length.pred = l.tl.length
      | [‹›] => by rfl
      | hd ::: tl => by
        simp [Nat.succ_add, Nat.pred_succ, Nat.zero_add]
        rfl

    theorem List.nth.length_none: ∀ n: Nat, ∀ l: List α, l.length = n → l.nth n = .none
      | _, [‹›], _ => by rfl
      | 0,     hd ::: tl, h => by
        have hf: 0 ≠ 0 := by
          calc 0
            _ = (hd ::: tl).length := by rw [h]
            _ = tl.length.succ     := by simp [Nat.add_comm, Nat.succ_eq_add_one, Nat.succ_ne_zero]
            _ ≠ 0                  := Nat.succ_ne_zero tl.length
        contradiction
      | n + 1, hd ::: tl, h => by
        have ih :=
          have h: tl.length = n := by
            calc tl.length
              _ = (hd ::: tl).length.pred := Eq.symm (List.tl.pred_length (hd ::: tl))
              _ = (n + 1).pred            := by rw [h]
          length_none n tl h
        calc (hd ::: tl).nth n.succ
          _ = tl.nth n := by rfl
          _ = .none    := by rw [ih]
  end Blended

  /-
  ### Church Numerals (Advanced)
  -/

  namespace Church
      def CNat: Type 1 := ∀ α: Type, (α → α) → α → α

      def CNat.succ: CNat → CNat
        | n, _, succ, x => succ (n _ succ x)

      def CNat.add: CNat → CNat → CNat
        | n₁, n₂, _, succ, x => n₁ _ succ (n₂ _ succ x)

      def CNat.mul: CNat → CNat → CNat
        | n₁, n₂, _, succ, x => n₁ _ (n₂ _ succ) x

      def CNat.exp: CNat → CNat → CNat
        | n₁, n₂, _, succ, x => sorry

      def CNat.toNat (n: CNat): Nat := n Nat Nat.succ 0

      instance: Add CNat where add := CNat.add
      instance: Mul CNat where mul := CNat.mul
      instance: Pow CNat CNat where pow := CNat.exp
      instance: Coe CNat Nat where coe := CNat.toNat

      section
        private def zero: CNat
          | _, _, x => x

        private def one: CNat
          | _, succ, x => succ x

        private def two: CNat
          | _, succ, x => succ (succ x)

        private def three: CNat
          | _, succ, x => succ (succ (succ x))

        example: (zero: Nat) = 0 := rfl
        example: (one: Nat) = 1 := rfl
        example: (two: Nat) = 2 := rfl

        example: CNat.succ zero = one  := rfl
        example: CNat.succ one = two   := rfl
        example: CNat.succ two = three := rfl

        example: zero + one = one := rfl
        example: two + three = three + two := rfl
        example: (two + two) + three = one + (three + three) := rfl

        example: one * one = one := rfl
        example: zero * (three + three) = zero := rfl
        example: two * three = three + three := rfl

        -- #eval (two ^ zero) Nat Nat.succ 0
        -- #eval (two ^ one) Nat Nat.succ 0
        -- #eval (two ^ two) Nat Nat.succ 0
        -- #eval (two ^ three) Nat Nat.succ 0

        -- example: two ^ two = two + two := rfl
        -- example: three ^ zero = one := rfl
        -- example: three ^ two = (two * (two * two)) + one := rfl
      end
  end Church
end SoftwareFoundations.LogicalFoundations.Poly
