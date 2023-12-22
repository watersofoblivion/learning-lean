/-
# Lists
-/

import «SoftwareFoundations».«LogicalFoundations».«Induction»

namespace NatList
  /-
  ## Pairs of Numbers
  -/

  structure NatProd: Type where
    n₁: Nat
    n₂: Nat
  deriving Repr

  def NatProd.fst (p: NatProd): Nat := p.1
  def NatProd.snd (p: NatProd): Nat := p.2
  def NatProd.swap (p: NatProd): NatProd := ⟨p.2, p.1⟩

  def threeFive: NatProd := ⟨3, 5⟩
  example: threeFive.fst = 3 := by rfl
  example: threeFive.snd = 5 := by rfl
  example: threeFive.swap = ⟨5, 3⟩ := by rfl

  theorem NatProd.surjectivePairing (p: NatProd): p = ⟨p.fst, p.snd⟩ := by
    rfl

  /-
  #### Exercises
  -/

  theorem NatProd.sndFstIsSwap (p: NatProd): p.swap = ⟨p.snd, p.fst⟩ := by
    rfl
  theorem NatProd.fstSwapIsSnd (p: NatProd): p.swap.fst = p.snd := by
    rfl

  /-
  ## Lists of Numbers
  -/

  inductive NatList: Type where
    | nil: NatList
    | cons: Nat → NatList → NatList
  deriving Repr

  def empty: NatList := .nil
  def list: NatList := .cons 1 (.cons 2 (.cons 3 .nil))
  def list2: NatList := .cons 4 (.cons 5 (.cons 6 .nil))

  def NatList.rpt (n: Nat): Nat → NatList
    | .zero => .nil
    | .succ count => .cons n (rpt n count)

  def NatList.length: NatList → Nat
    | .nil => 0
    | .cons _ tl => 1 + tl.length

  def NatList.append: NatList → NatList → NatList
    | .nil, l => l
    | .cons hd tl, l => .cons hd (tl.append l)

  example: list.append list2 = .cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 (.cons 6 .nil))))) := by rfl
  example: list.append .nil = list := by rfl
  example: empty.append list = list := by rfl

  def NatList.hd (default: Nat): NatList → Nat
    | .nil => default
    | .cons hd _ => hd

  def NatList.tl: NatList → NatList
    | .nil => .nil
    | .cons _ tl => tl

  example: list.hd 42 = 1 := by rfl
  example: empty.hd 42 = 42 := by rfl
  example: list.tl = .cons 2 (.cons 3 .nil) := by rfl
  example: empty.tl = empty := by rfl

  def NatList.filter (p: Nat → Bool): NatList → NatList
    | .nil => .nil
    | .cons hd tl =>
      if p hd
      then .cons hd (tl.filter p)
      else tl.filter p

  def NatList.nonZeros: NatList → NatList := NatList.filter (λ elem => elem != 0)
  def NatList.oddMembers: NatList → NatList := NatList.filter (λ elem => elem % 2 = 1)

  def list3: NatList := .cons 0 (.cons 1 (.cons 0 (.cons 2 (.cons 3 (.cons 0 (.cons 0 .nil))))))
  example: list3.nonZeros = list := by rfl
  example: empty.nonZeros = empty := by rfl
  example: list3.oddMembers = .cons 1 (.cons 3 .nil) := by rfl
  example: empty.oddMembers = empty := by rfl

  def NatList.countOddMembers (l: NatList): Nat := l.oddMembers.length
  example: list3.countOddMembers = 2 := by rfl
  example: (list3.append list3).countOddMembers = 4 := by rfl
  example: empty.countOddMembers = 0 := by rfl

  def NatList.alternate: NatList → NatList → NatList
    | .nil, l | l, .nil => l
    | .cons hd₁ tl₁, .cons hd₂ tl₂ => .cons hd₁ (.cons hd₂ (alternate tl₁ tl₂))

  def list4: NatList := (NatList.cons 1 .nil)
  example: list.alternate list2 = .cons 1 (.cons 4 (.cons 2 (.cons 5 (.cons 3 (.cons 6 .nil))))) := by rfl
  example: list4.alternate list2 = .cons 1 list2 := by rfl
  example: list2.alternate list4 = .cons 4 (.cons 1 (.cons 5 (.cons 6 .nil))) := by rfl
  example: empty.alternate list2 = list2 := by rfl

  /-
  ### Bags vs. Lists
  -/

  abbrev Bag := NatList

  def Bag.count (v: Nat): Bag → Nat
    | .nil => 0
    | .cons hd tl =>
      if hd == v
      then 1 + count v tl
      else count v tl

  def emptyBag: Bag := empty
  def bag: Bag := list
  def bag2: Bag := list2
  def bag3: Bag := list3
  def bag4: Bag := list4

  example: bag.count 1 = 1 := by rfl
  example: bag3.count 0 = 4 := by rfl
  example: bag3.count 42 = 0 := by rfl

  def Bag.sum (b₁ b₂: Bag): Bag := b₁.append b₂
  def Bag.add (v: Nat) (b: Bag): Bag := .cons v b
  def Bag.member (v: Nat): Bag → Bool
    | .nil => false
    | .cons hd tl =>
      if hd == v
      then true
      else member v tl

  example: (bag.sum bag).count 1 = 2 := by rfl
  example: (bag.sum bag2).count 1 = 1 := by rfl
  example: (bag.add 1).count 1 = 2 := by rfl
  example: (bag.add 1).count 5 = 0 := by rfl
  example: bag.member 1 = true := by rfl
  example: bag.member 42 = false := by rfl

  def Bag.removeOne (v: Nat): Bag → Bag
    | .nil => .nil
    | .cons hd tl =>
      if hd == v
      then tl
      else .cons hd (removeOne v tl)

  example: (bag3.removeOne 0).count 0 = 3 := by rfl
  example: (bag3.removeOne 42).count 0 = 4 := by rfl
  example: (emptyBag.removeOne 42).count 0 = 0 := by rfl

  def Bag.removeAll (v: Nat): Bag → Bag
    | .nil => .nil
    | .cons hd tl =>
      if hd == v
      then removeAll v tl
      else .cons hd (removeAll v tl)

  example: (bag3.removeAll 0).count 0 = 0 := by rfl
  example: (bag3.removeAll 1).count 0 = 4 := by rfl

  def Bag.included: Bag → Bag → Bool
    | .nil, _ => true
    | _, .nil => false
    | .cons hd tl, b =>
      if Bag.member hd b
      then Bag.included tl (Bag.removeOne hd b)
      else false

  def tgt: Bag := .cons 2 (.cons 1 (.cons 4 (.cons 1 .nil)))

  example: Bag.included (.cons 1 (.cons 2 .nil)) tgt = true := by rfl
  example: Bag.included (.cons 1 (.cons 2 (.cons 2 .nil))) tgt = false := by rfl

  theorem Bag.addIncCount (b: Bag) (n: Nat): (b.add n).length = b.length + 1 := by
    induction b with
      | nil => rfl
      | cons hd tl ih =>
        simp [Bag.add, NatList.length] at ih
        simp [NatList.length, Bag.add, ih]
        rw [Nat.add_comm]

  /-
  ## Reasoning About Lists
  -/

  theorem NatList.nilAppend (l: NatList): NatList.nil.append l = l := by
    rfl

  theorem NatList.tlLengthPred (l: NatList): l.length.pred = l.tl.length := by
    cases l with
      | nil => rfl
      | cons hd tl =>
        rw [NatList.length]
        rw [← Nat.add_comm, ← Nat.succ_eq_add_one, Nat.pred_succ]
        rfl

  theorem NatList.appAssoc (l₁ l₂ l₃: NatList): (l₁.append l₂).append l₃ = l₁.append (l₂.append l₃) := by
    induction l₁ with
      | nil => rfl
      | cons hd tl ihₗ =>
        simp [NatList.append]
        rw [ihₗ]

  def NatList.rev: NatList -> NatList
    | .nil => .nil
    | .cons hd tl => tl.rev.append (.cons hd .nil)

  theorem NatList.appLength (l₁ l₂: NatList): (l₁.append l₂).length = l₁.length + l₂.length := by
    induction l₁ with
      | nil =>
        rw [NatList.length, NatList.append]
        simp
      | cons hd tl ihₗ =>
        rw [NatList.append, NatList.length, NatList.length]
        rw [ihₗ]
        rw [Nat.add_assoc]

  theorem NatList.revLength (l: NatList): l.rev.length = l.length := by
    induction l with
      | nil => rfl
      | cons hd tl ihₗ =>
        simp [NatList.rev, NatList.length, NatList.appLength, Nat.add_comm]
        rw [ihₗ]

  /-
  ### Search
  -/

  -- No Lean eqivalent?

  /-
  #### Exercises
  -/

  theorem NatList.appNilRight (l: NatList): l.append .nil = l := by
    induction l with
      | nil => rfl
      | cons hd tl ihₗ =>
        rw [NatList.append]
        rw [ihₗ]

  theorem NatList.revAppDistr (l₁ l₂: NatList): (l₁.append l₂).rev = l₂.rev.append l₁.rev := by
    induction l₁ with
      | nil =>
        rw [NatList.append, NatList.rev, NatList.appNilRight]
      | cons hd tl ihₗ =>
        simp [NatList.append, NatList.rev, NatList.appAssoc]
        rw [ihₗ]
        simp [NatList.appAssoc]

  theorem NatList.revInvolute (l: NatList): l.rev.rev = l := by
    induction l with
      | nil => rfl
      | cons hd tl ihₗ =>
        simp [NatList.rev, NatList.revAppDistr, NatList.appAssoc, NatList.append]
        rw [ihₗ]

  theorem NatList.appAssoc4 (l₁ l₂ l₃ l₄: NatList): l₁.append (l₂.append (l₃.append l₄)) = ((l₁.append l₂).append l₃).append l₄ := by
    simp [NatList.appAssoc]

  theorem NatList.filterTheorem (l₁ l₂: NatList) (p: Nat → Bool): (l₁.append l₂).filter p = (l₁.filter p).append (l₂.filter p) := by
    induction l₁ with
      | nil =>
        simp [NatList.nilAppend, NatList.filter]
      | cons hd tl ihₗ =>
        rw [NatList.append, NatList.filter, NatList.filter]
        rw [ihₗ]
        rw [← NatList.append]
        cases p hd <;> simp

  theorem NatList.nonZerosApp (l₁ l₂: NatList): (l₁.append l₂).nonZeros = l₁.nonZeros.append l₂.nonZeros := by
    cases l₁ with
      | nil =>
        rw [NatList.nilAppend, NatList.nonZeros, NatList.filter, NatList.append]
      | cons hd tl =>
        rw [NatList.append, NatList.nonZeros, NatList.filter, filterTheorem]
        cases hd <;> rfl

  def NatList.beq: NatList → NatList → Bool
    | .nil, .nil => true
    | .cons hd₁ tl₁, .cons hd₂ tl₂ =>
      hd₁ == hd₂ && tl₁.beq tl₂
    | _, _ => false

  example: empty.beq empty := by rfl
  example: list.beq list := by rfl

  theorem NatList.beqRefl (l: NatList): l.beq l := by
    induction l with
      | nil => rfl
      | cons hd tl ihₗ =>
        rw [NatList.beq]
        simp
        rw [ihₗ]

  theorem Bag.countMembersNonZero (b: NatList): Nat.less_eq 1 (Bag.count 1 (NatList.cons 1 b)) := by
    induction b with
      | nil => rfl
      | cons hd tl ihb => sorry

  theorem Nat.ltSucc (n: Nat): Nat.less_eq n n.succ := by
    induction n with
      | zero => rfl
      | succ n ihₙ =>
        rw [Nat.less_eq, ← Nat.succ_eq_add_one]
        rw [ihₙ]

  theorem Bag.removeDoesNotIncreaseCount (b: Bag): Nat.less_eq ((Bag.removeOne 0 b).count 0) (b.count 0) := by
    induction b with
      | nil => rfl
      | cons hd tl ihb =>
        sorry

  theorem involutionInjective (f: Nat → Nat) (h₁: ∀ (n: Nat), n = f (f n)) (n₁ n₂: Nat) (h₂: f n₁ = f n₂): n₁ = n₂ := by
    sorry

  theorem NatList.revInjective (l₁ l₂: NatList) (h: l₁.rev = l₂.rev): l₁ = l₂ := by
    sorry

  /-
  ## Options
  -/

  inductive NatOption: Type where
    | none: NatOption
    | some: Nat → NatOption
  deriving Repr

  def NatOption.elim (default: Nat): NatOption → Nat
    | .none => default
    | .some n => n

  def NatList.nthOpt: Nat → NatList → NatOption
    | _, .nil => .none
    | .zero, .cons hd _ => .some hd
    | .succ n, .cons _ tl => tl.nthOpt n

  example: list2.nthOpt 0 = .some 4 := by rfl
  example: list2.nthOpt 1 = .some 5 := by rfl
  example: list2.nthOpt 2 = .some 6 := by rfl
  example: list2.nthOpt 3 = .none := by rfl

  def NatList.hdOpt: NatList → NatOption
    | .nil => .none
    | .cons hd _ => .some hd

  example: list.hdOpt = .some 1 := by rfl
  example: list2.hdOpt = .some 4 := by rfl
  example: empty.hdOpt = .none := by rfl

  theorem NatList.hdOptElim (l: NatList) (default: Nat): l.hd default = l.hdOpt.elim default := by
    cases l with
      | nil => rfl
      | cons hd tl => rw [NatList.hd, NatList.hdOpt, NatOption.elim]
end NatList

namespace PartialMap
  open NatList

  structure Key: Type where
    n: Nat
  deriving Repr

  def Key.beq (k₁ k₂: Key): Bool := k₁.n.beq k₂.n

  theorem Key.beqRefl (k: Key): k.beq k := by
    simp [Key.beq]

  inductive PartialMap: Type where
    | empty: PartialMap
    | record: Key → Nat → PartialMap → PartialMap

  def PartialMap.update (m: PartialMap) (k: Key) (v: Nat): PartialMap :=
    .record k v m

  def PartialMap.find (k: Key): PartialMap → NatOption
    | .empty => .none
    | .record kₘ v m => if kₘ.beq k then .some v else m.find k

  theorem PartialMap.updateEq (m: PartialMap) (k: Key) (v: Nat): (m.update k v).find k = .some v := by
    cases m <;> simp [PartialMap.update, PartialMap.find, Key.beq]

  theorem PartialMap.updateNeq (m: PartialMap) (k₁ k₂: Key) (v: Nat) (h: k₁.beq k₂ == false): (m.update k₁ v).find k₂ = m.find k₂ := by
    sorry
    -- cases m with
    --   | empty =>
    --     rw [PartialMap.update, PartialMap.find, PartialMap.find]
    --   | record kₘ vₘ mₘ =>
    --     rw [PartialMap.update, PartialMap.find, PartialMap.find]
end PartialMap

-- □ ◇ ○
-- ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ
-- αβγδεζηθικλμνξοπρστυφχψω

-- type List (α: *) (l: Nat) =
--   | nil: List α 0
--   | cons (n: Nat): α → List α n → List α (n + 1)

-- 𝕐 𝕃

--
