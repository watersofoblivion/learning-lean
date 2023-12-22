/-
# Axioms and Computation
-/

/-
## Historical and Philosophical Context
-/

/-
## Propositional Extensionality
-/

-- axiom propext {a b: Prop}: (a ↔ b) → a = b

example (a b c d e: Prop) (h: a ↔ b): (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

example (a b: Prop) (p: Prop → Prop) (h₁: a ↔ b) (h₂: p a): p b :=
  propext h₁ ▸ h₂

/-
## Function Extensionality
-/

universe u v
#check @funext
#check (@funext: {α: Type u} → {β: α → Type u} → {f g: (x: α) → β x} → (∀ x: α, f x = g x) → f = g)
#print funext

def Set (α: Type u) := α → Prop

def Set.mem (x: α) (s: Set α) := s x
infix:50 (priority := high) "∈" => Set.mem

theorem Set.ext {a b: Set α} (h: ∀ x: α, x ∈ a ↔ x ∈ b): a = b :=
  funext (fun x => propext (h x))

def Set.empty: Set α := fun _ => False
notation (priority := high) "∅" => Set.empty

def Set.inter (a b: Set α): Set α :=
  fun x => x ∈ a ∧ x ∈ b
infix:70 "∩" => Set.inter

example (a: Set α): a ∩ a = a :=
  Set.ext fun _ => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

example (a: Set α): a ∩ ∅ = ∅ :=
  Set.ext fun _ => Iff.intro
    (fun ⟨_, h⟩ => h)
    False.elim

example (a: Set α): ∅ ∩ a = ∅ :=
  Set.ext fun _ => Iff.intro
    (fun ⟨h, _⟩ => h)
    False.elim

example (a b: Set α): a ∩ b = b ∩ a :=
  Set.ext fun _ => Iff.intro
    (fun ⟨ha, hb⟩ => ⟨hb, ha⟩)
    (fun ⟨hb, ha⟩ => ⟨ha, hb⟩)

def f (x: Nat) := x
def g (x: Nat) := 0 + x

def val: Nat :=
  Eq.recOn (motive := fun _ _ => Nat) fEqG 0
  where
    fEqG: f = g := funext fun x => (Nat.zero_add x).symm

#reduce val
#eval val

def val2: Nat :=
  Eq.recOn (motive := fun _ _ => Nat) ttEq 0
  where
    ttEq: (True ∧ True) = True :=
      propext (Iff.intro
        (fun ⟨h, _⟩ => h)
        (fun h => ⟨h, h⟩))

#reduce val2
#eval val2

/-
## Quotients
-/

-- axiom Quot: {α: Sort u} → (α → α → Prop) → Sort u
-- axiom Quot.mk: {α: Sort u} → (r: α → α → Prop) → α → Quot r
-- axiom Quot.ind: ∀ {α: Sort u} {r: α → α → Prop} {β: Quot r → Prop}, (∀ a b, r a b → f a = f b) → Quot r → β
-- axiom Quot.lift: {α: Sort u} → {r: α → α → Prop} → {β: Sort u} → (f: α → β) → (∀ a b, r a b → f a = f b) → Quot r → β

def mod7Rel (x y: Nat): Prop :=
  x % 7 = y % 7

#check Quot mod7Rel
#check Quot.mk mod7Rel 4

def f2 (x: Nat): Bool := x % 7 = 0

theorem f2_respects (a b: Nat) (h: mod7Rel a b): f2 a = f2 b := by
  simp [mod7Rel, f2] at *
  rw [h]

#check Quot.lift f2 f2_respects

example (a: Nat): Quot.lift f2 f2_respects (Quot.mk mod7Rel a) = f2 a := rfl

-- axiom Quot.sound: ∀ {α: Type u} {r: α → α → Prop} {a b: α}, r a b → Quot.mk r a = Quot.mk r b

namespace Hidden
  -- class Setoid (α: Sort u) where
  --   r: α → α → Prop
  --   isEquiv: Equivalence r

  instance {α: Sort u} [Setoid α]: HasEquiv α := ⟨Setoid.r⟩

  section
    variable {α: Sort u} [Setoid α]

    example (x: α): x ≈ x :=
      Setoid.iseqv.refl x

    example {a b: α} (hab: a ≈ b): b ≈ a :=
      Setoid.iseqv.symm hab

    example {a b c: α} (hab: a ≈ b) (hbc: b ≈ c): a ≈ c :=
      Setoid.iseqv.trans hab hbc
  end

  -- def Quotient {α: Sort u} (s: Setoid α) := @Quot α Setoid.r

  #check Quotient.exact

  private def eqv (p₁ p₂: α × α): Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
  infix:50 "~" => eqv

  private theorem eqv.refl (p: α × α): p ~ p :=
    Or.inl ⟨rfl, rfl⟩
  private theorem eqv.symm: ∀ {p₁ p₂: α × α}, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂), (b₁, b₂), .inl ⟨a₁b₁, a₂b₂⟩ => .inl (by simp_all)
    | (a₁, a₂), (b₁, b₂), .inr ⟨a₁b₂, a₂b₁⟩  => .inr (by simp_all)
  private theorem eqv.trans: ∀ {p₁ p₂ p₃: α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂), (b₁, b₂), (c₁, c₂), .inl ⟨a₁b₁, a₂b₂⟩, .inl ⟨b₁c₁, b₂c₂⟩ => .inl (by simp_all)
    | (a₁, a₂), (b₁, b₂), (c₁, c₂), .inl ⟨a₁b₁, a₂b₂⟩, .inr ⟨b₁c₂, b₂c₁⟩ => .inr (by simp_all)
    | (a₁, a₂), (b₁, b₂), (c₁, c₂), .inr ⟨a₁b₂, a₂b₁⟩, .inl ⟨b₁c₁, b₂c₂⟩ => .inr (by simp_all)
    | (a₁, a₂), (b₁, b₂), (c₁, c₂), .inr ⟨a₁b₂, a₂b₁⟩, .inr ⟨b₁c₂, b₂c₁⟩ => .inl (by simp_all)

  private theorem is_equivalence: Equivalence (@eqv α) :=
    { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

  instance uprodSetoid (α: Type u): Setoid (α × α) where
    r := eqv
    iseqv := is_equivalence

  def UProd (α: Type u): Type u :=
    Quotient (uprodSetoid α)

  def UProd.mk {α: Type} (a₁ a₂: α): UProd α :=
    Quotient.mk' (a₁, a₂)

  notation "{" a₁ "," a₂ "}" => UProd.mk a₁ a₂

  theorem mk_eq_mk (a₁ a₂: α): {a₁, a₂} = {a₂, a₁} :=
    Quot.sound (Or.inr ⟨rfl, rfl⟩)

  private def mem_fn (a: α): α × α → Prop
    | (a₁, a₂) => a = a₁ ∨ a = a₂

  private theorem mem_swap {a: α}: ∀ {p: α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
    | (a₁, a₂) => by
      apply propext
      apply Iff.intro
      · intro
        | .inl h => exact Or.inr h
        | .inr h => exact Or.inl h
      · intro
        | .inl h => exact Or.inr h
        | .inr h => exact Or.inl h

  private theorem mem_respects: {p₁ p₂: α × α} → (a: α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
    | (a₁, a₂), (b₁, b₂), a, .inl ⟨a₁b₁, a₂b₂⟩ => by simp_all
    | (a₁, a₂), (b₁, b₂), a, .inr ⟨a₁b₂, a₂b₁⟩ => by
      simp_all
      apply mem_swap

  def mem (a: α) (u: UProd α): Prop :=
    Quot.liftOn u (fun p => mem_fn a p) (fun _ _ e => mem_respects a e)

  infix:50 (priority := high) "∈" => mem

  theorem mem_mk_left (a b: α): a ∈ {a, b} := Or.inl rfl
  theorem mem_mk_right (a b: α): b ∈ {a, b} := Or.inr rfl
  theorem mem_or_mem_of_mem_mk {a b c: α}: c ∈ {a, b} → c = a ∨ c = b :=
    fun h => h
end Hidden

/-
## Choice
-/

-- class inductive Nonempty (α: Sort u): Prop where
--   | intro (val: α): Nonempty α

example (α: Type u): Nonempty α ↔ ∃ _: α, True :=
  ⟨mp, mpr⟩
  where
    mp: Nonempty α → ∃ _: α, True
      | ⟨a⟩ => ⟨a, trivial⟩
    mpr: (∃ _: α, True) → Nonempty α
      | ⟨w, _⟩ => ⟨w⟩

-- axiom Classical.choice {α: Sort u}: Nonempty α → α

noncomputable def indefiniteDescription {α: Sort u} (p: α → Prop) (h: ∃ x: α, p x): { x // p x } :=
  Classical.choice <| let ⟨w, hpw⟩ := h; ⟨⟨w, hpw⟩⟩

noncomputable def choose {α: Sort u} {p: α → Prop} (h: ∃ x: α, p x): α :=
  (indefiniteDescription p h).val

theorem choose_spec {α: Sort u} {p: α → Prop} (h: ∃ x: α, p x): p (choose h) :=
  (indefiniteDescription p h).property

theorem inhabited_of_nonempty: Nonempty α → Inhabited α :=
  fun h => Classical.choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)

#check @Classical.strongIndefiniteDescription

#check @Classical.epsilon
#check @Classical.epsilon_spec

/-
## The Law of the Excluded Middle
-/

#check @Classical.em
