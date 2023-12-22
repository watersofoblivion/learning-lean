/-
# Quantifiers and Equality
-/

namespace QuantifiersAndEquality

/-
## The Universal Quantifier
-/

section UniversalQuantifier
  example (α: Type) (p q: α → Prop): (∀ x: α, p x ∧ q x) → ∀ y: α, p y :=
    fun h: ∀ x: α, p x ∧ q x =>
    fun y: α =>
    show p y from (h y).left

  example: ∀ n: Nat, 0 + n = n := Nat.zero_add

  example (α: Type) (p q: α → Prop): (∀ x: α, p x ∧ q x) → ∀ x: α, p x :=
    fun h: ∀ x: α, p x ∧ q x =>
    fun z: α =>
    show p z from (h z).left

  variable (α: Type) (r: α → α → Prop)
  variable (refl_r: ∀ {x: α}, r x x)
  variable (symm_r: ∀ {x y: α}, r x y → r y x)
  variable (trans_r: ∀ {x y z: α}, r x y → r y z → r x z)

  variable (a b c: α)
  variable (hab: r a b) (hbc: r b c)

  #check @trans_r
  #check @trans_r a b c
  #check @trans_r a b c hab
  #check @trans_r a b c hab hbc

  #check trans_r
  #check trans_r hab
  #check trans_r hab hbc

  example (a b c d: α) (hab: r a b) (hcb: r c b) (hcd: r c d): r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd
end UniversalQuantifier

/-
## Equality
-/

section Equality
  #check Eq.refl
  #check Eq.symm
  #check Eq.trans

  universe u
  #check @Eq.refl.{u}
  #check @Eq.symm.{u}
  #check @Eq.trans.{u}

  variable (α: Type) (a b c d: α)
  variable (hab: a = b) (hcb: c = b) (hcd: c = d)

  example: a = d :=
    Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
  example: a = d :=
    (hab.trans hcb.symm).trans hcd

  variable (α β: Type)

  example (f: α → β) (a: α): (fun x => f x) a = f a := Eq.refl _
  example (a: α) (b: β): (a, b).1 = a := Eq.refl _
  example: 2 + 3 = 5 := Eq.refl _

  example (f: α → β) (a: α): (fun x => f x) a = f a := rfl
  example (a: α) (b: β): (a, b).1 = a := rfl
  example: 2 + 3 = 5 := rfl

  example (α: Type) (a b: α) (p: α → Prop) (h₁: a = b) (h₂: p a): p b :=
    Eq.subst h₁ h₂
  example (α: Type) (a b: α) (p: α → Prop) (h₁: a = b) (h₂: p a): p b :=
    h₁ ▸ h₂

  variable (α: Type)
  variable (a b: α)
  variable (f g: α → Nat)
  variable (h₁: a = b)
  variable (h₂: f = g)

  example: f a = f b := congrArg f h₁
  example: f a = g a := congrFun h₂ a
  example: f a = g b := congr h₂ h₁

  variable (a b c: Nat)

  example: a + 0 = a := Nat.add_zero a
  example: 0 + a = a := Nat.zero_add a
  example: a * 1 = a := Nat.mul_one a
  example: 1 * a = a := Nat.one_mul a
  example: a + b = b + a := Nat.add_comm a b
  example: (a + b) + c = a + (b + c) := Nat.add_assoc a b c
  example: a * b = b * a := Nat.mul_comm a b
  example: (a * b) * c = a * (b * c) := Nat.mul_assoc a b c
  example: a * (b + c) = (a * b) + (a * c) := Nat.left_distrib a b c
  example: a * (b + c) = (a * b) + (a * c) := Nat.mul_add a b c
  example: (a + b) * c = (a * c) + (b * c) := Nat.right_distrib a b c
  example: (a + b) * c = (a * c) + (b * c) := Nat.add_mul a b c

  example (x y: Nat): (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    have h₁: (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
      Nat.left_distrib (x + y) x y
    have h₂: (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
      (Nat.right_distrib x y x) ▸ (Nat.right_distrib x y y) ▸ h₁
    h₂.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
end Equality

/-
## Calculational Proofs
-/

section CalculationalProofs
  variable (a b c d e: Nat)
  variable (h₁: a = b)
  variable (h₂: b = c + 1)
  variable (h₃: c = d)
  variable (h₄: e = 1 + d)

  example: a = e :=
    calc
      a = b     := h₁
      _ = c + 1 := h₂
      _ = d + 1 := congrArg Nat.succ h₃
      _ = 1 + d := Nat.add_comm d 1
      _ = e     := Eq.symm h₄

  example: a = e :=
    calc
      a = b     := by rw [h₁]
      _ = c + 1 := by rw [h₂]
      _ = d + 1 := by rw [h₃]
      _ = 1 + d := by rw [Nat.add_comm]
      _ = e     := by rw [h₄]

  example: a = e :=
    calc
      a = d + 1 := by rw [h₁, h₂, h₃]
      _ = 1 + d := by rw [Nat.add_comm]
      _ = e     := by rw [h₄]

  example: a = e := by
    rw [h₁, h₂, h₃, Nat.add_comm, h₄]

  example: a = e := by
    simp [h₁, h₂, h₃, Nat.add_comm, h₄]

  example (a b c d: Nat) (h₁: a = b) (h₂: b ≤ c) (h₃: c + 1 < d): a < d :=
    calc
      a = b     := h₁
      _ ≤ c     := h₂
      _ < c + 1 := Nat.lt_succ_self c
      _ < d     := h₃

  def divides (x y: Nat): Prop := ∃ k: Nat, k * x = y

  def divides_trans (h₁: divides x y) (h₂: divides y z): divides x z :=
    let ⟨k₁, d₁⟩ := h₁
    let ⟨k₂, d₂⟩ := h₂
    ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

  def divides_mul (x k: Nat): divides x (k * x) :=
    ⟨k, rfl⟩

  instance: Trans divides divides divides where
    trans := divides_trans

  example (h₁: divides x y) (h₂: y = z): divides x (2 * z) :=
    calc
      divides x y := h₁
      _ = z       := h₂
      divides _ (2 * z) := divides_mul ..

  infix:50 "∣" => divides

  example (h₁: x ∣ y) (h₂: y = z): x ∣ (2 * z) :=
    calc
      x ∣ y       := h₁
      _ = z       := h₂
      _ ∣ (2 * z) := divides_mul ..

  example (x y: Nat): (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc
      (x + y) * (x + y) = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y               := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y)           := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y             := by rw [←Nat.add_assoc]

  example (x y: Nat): (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc (x + y) * (x + y)
      _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]

  example (x y: Nat): (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
    rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

  example (x y: Nat): (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
    simp [Nat.mul_add, Nat.add_mul, ←Nat.add_assoc]
end CalculationalProofs

/-
## The Existential Quantifier
-/

section ExistentialQuantifier
  example: ∃ n: Nat, n > 0 :=
    have h: 1 > 0 := Nat.zero_lt_succ 0
    Exists.intro 1 h
  example: ∃ n: Nat, n > 0 :=
    have h: 1 > 0 := Nat.zero_lt_succ 0
    ⟨1, h⟩

  example (n₁: Nat) (h: n₁ > 0): ∃ n₂: Nat, n₂ < n₁ :=
    Exists.intro 0 h
  example (n₁: Nat) (h: n₁ > 0): ∃ n₂: Nat, n₂ < n₁ :=
    ⟨0, h⟩

  example (n₁ n₂ n₃: Nat) (h₁₂: n₁ < n₂) (h₂₃: n₂ < n₃): ∃ n₄: Nat, n₁ < n₄ ∧ n₄ < n₃ :=
    Exists.intro n₂ ⟨h₁₂, h₂₃⟩
  example (n₁ n₂ n₃: Nat) (h₁₂: n₁ < n₂) (h₂₃: n₂ < n₃): ∃ n₄: Nat, n₁ < n₄ ∧ n₄ < n₃ :=
    ⟨n₂, h₁₂, h₂₃⟩

  #check Exists.intro

  variable (g: Nat → Nat → Nat)
  variable (hg: g 0 0 = 0)

  theorem gExample₁: ∃ x: Nat, g x x = x := ⟨0, hg⟩
  theorem gExample₂: ∃ x: Nat, g x 0 = x := ⟨0, hg⟩
  theorem gExample₃: ∃ x: Nat, g 0 0 = x := ⟨0, hg⟩
  theorem gExample₄: ∃ x: Nat, g x x = 0 := ⟨0, hg⟩

  set_option pp.explicit true
  #print gExample₁
  #print gExample₂
  #print gExample₃
  #print gExample₄

  variable (α: Type)
  variable (p q: α → Prop)

  example (h: ∃ x: α, p x ∧ q x): ∃ x: α, q x ∧ p x :=
    Exists.elim h
      fun w (hw: p w ∧ q w) =>
        show ∃ x, q x ∧ p x from ⟨w, ⟨hw.right, hw.left⟩⟩

  example: (∃ x: α, p x ∧ q x) → ∃ x: α, q x ∧ p x
    | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

  example (h: ∃ x: α, p x ∧ q x): ∃ x: α, q x ∧ p x :=
    match h with
      | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

  example (h: ∃ x: α, p x ∧ q x): ∃ x: α, q x ∧ p x :=
    let ⟨w, hpw, hqw⟩ := h
    ⟨w, hqw, hpw⟩

  example: (∃ x: α, p x ∧ q x) → ∃ x: α, q x ∧ p x
    | ⟨(w: α), (hw: p w ∧ q w)⟩ => ⟨w, ⟨hw.right, hw.left⟩⟩

  example: (∃ x: α, p x ∧ q x) → ∃ x: α, q x ∧ p x :=
    fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

  def isEven (n₁: Nat) := ∃ n₂: Nat, n₁ = 2 * n₂

  theorem evenPlusEven (h₁: isEven n₁) (h₂: isEven n₂): isEven (n₁ + n₂) :=
    Exists.elim h₁ (fun w₁ (hw₁: n₁ = 2 * w₁) =>
    Exists.elim h₂ (fun w₂ (hw₂: n₂ = 2 * w₂) =>
      Exists.intro (w₁ + w₂)
        (calc n₁ + n₂
          _ = 2 * w₁ + 2 * w₂ := by rw [hw₁, hw₂]
          _ = 2 * (w₁ + w₂)   := by rw [Nat.mul_add])))

  example: isEven n₁ → isEven n₂ → isEven (n₁ + n₂)
    | ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ => ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩
end ExistentialQuantifier

section ClassicalLogic
  open Classical

  variable (p q: α → Prop)
  variable (r: Prop)

  example (h: ¬∀ x: α, ¬p x): ∃ x: α, p x :=
    byContradiction
      fun h₁: ¬∃ x, p x =>
        have h₂: ∀ x: α, ¬p x :=
          fun x (h₃: p x) =>
            have h₄: ∃ x: α, p x := ⟨x, h₃⟩
            show False from h₁ h₄
        show False from h h₂

  example: (∃ _: α, r) → r
    | ⟨_, hw⟩ => hw

  example (a: α): r → (∃ _: α, r)
    | hr => ⟨a, hr⟩

  example: (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
    have mp: (∃ x, p x ∧ r) → (∃ x, p x) ∧ r
      | ⟨w, ⟨hpx, hr⟩⟩ => ⟨⟨w, hpx⟩, hr⟩
    have mpr: (∃ x, p x) ∧ r → (∃ x, p x ∧ r)
      | ⟨⟨w, hpx⟩, hr⟩ => ⟨w, ⟨hpx, hr⟩⟩
    ⟨mp, mpr⟩

  example: (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    have mp: (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
      | ⟨w, .inl hw⟩ => .inl ⟨w, hw⟩
      | ⟨w, .inr hw⟩ => .inr ⟨w, hw⟩
    have mpr: (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x)
      | .inl ⟨w, hw⟩ => ⟨w, .inl hw⟩
      | .inr ⟨w, hw⟩ => ⟨w, .inr hw⟩
    ⟨mp, mpr⟩

  example: (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    have mp (hxpx: ∀ x, p x): ¬ (∃ x, ¬ p x) :=
      fun ⟨x, hnpx⟩ =>
        have hpx: p x := hxpx x
        absurd hpx hnpx
    have mpr (hnpx: ¬ (∃ x, ¬ p x)): ∀ x, p x :=
      fun (x: α) =>
        byContradiction
          fun (h: ¬p x) =>
            False.elim (hnpx ⟨x, h⟩)
    ⟨mp, mpr⟩

  example: (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    have mp: (∃ x, p x) → ¬ (∀ x, ¬ p x)
      | ⟨w, px⟩ =>
        fun hxpx: ∀ x, ¬p x => absurd px (hxpx w)
    have mpr (hnxnpx: ¬ (∀ x, ¬ p x)): ∃ x, p x :=
      sorry
    ⟨mp, mpr⟩

  example: (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    have mp (hnexpx: ¬ ∃ x, p x): ∀ x, ¬ p x := sorry
    have mpr (haxnpx: ∀ x, ¬ p x): ¬ ∃ x, p x := sorry
    ⟨mp, mpr⟩

  example: (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    have mp: (¬ ∀ x, p x) → (∃ x, ¬ p x) := sorry
    have mpr: (∃ x, ¬ p x) → ¬ ∀ x, p x
      | ⟨w, hnpx⟩ =>
        fun (h: ∀ x, p x) => absurd (h w) hnpx
    ⟨mp, mpr⟩

  example: (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    have mp (pxr: ∀ x, p x → r): (∃ x, p x) → r :=
      fun ⟨w, hpx⟩ => pxr w hpx
    have mpr (pxr: (∃ x, p x) → r): (∀ x, p x → r) :=
      fun hx hpx => pxr ⟨hx, hpx⟩
    ⟨mp, mpr⟩

  example (a: α): (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    have mp: (∃ x, p x → r) → (∀ x, p x) → r
      | ⟨w, hpxr⟩, axpx => hpxr (axpx w)
    have mpr: ((∀ x, p x) → r) → (∃ x, p x → r) := sorry
    ⟨mp, mpr⟩

  example (a: α): (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    have mp: (∃ x, r → p x) → (r → ∃ x, p x)
      | ⟨w, hrpx⟩ => fun (hr: r) => ⟨w, hrpx hr⟩
    have mpr: (r → ∃ x, p x) → (∃ x, r → p x) := sorry
    ⟨mp, mpr⟩
end ClassicalLogic

/-
## More on the Proof Language
-/

section MoreProofLanguage
  variable (f: Nat → Nat)
  variable (h: ∀ x: Nat, f x ≤ f (x + 1))

  example: f 0 ≤ f 3 :=
    have: f 0 ≤ f 1 := h 0
    have: f 0 ≤ f 2 := Nat.le_trans this (h 1)
    show f 0 ≤ f 3 from Nat.le_trans this (h 2)

  example: f 0 ≤ f 3 :=
    have: f 0 ≤ f 1 := h 0
    have: f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
    show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

  example (h₁: f 0 ≥ f 1) (h₂: f 1 ≥ f 2): f 0 = f 2 :=
    have: f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
    have: f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
    show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

  example (n: Nat): Nat := ‹Nat›
end MoreProofLanguage

/-
# Exercises
-/

/-
## 1
-/

section ExerciseOne
  variable (α: Type) (p q: α → Prop)

  example: (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := -- sorry
    have mp (h: ∀ x, p x ∧ q x): (∀ x, p x) ∧ (∀ x, q x) :=
      have px x := (h x).left
      have qx x := (h x).right
      ⟨px, qx⟩
    have mpr: (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x)
      | ⟨hx, qx⟩ => fun x => ⟨hx x, qx x⟩
    ⟨mp, mpr⟩

  example: (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x)
    | pxqx, px => fun x => pxqx x (px x)

  example: (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x
    | .inl px => fun x => .inl (px x)
    | .inr qx => fun x => .inr (qx x)
end ExerciseOne

/-
## 2
-/

section ExerciseTwo
  variable (α: Type) (p q: α → Prop)
  variable (r: Prop)

  example (y: α): ((∀ _: α, r) ↔ r) :=
    have mp (xr: ∀ _: α, r): r := xr y
    have mpr (hr: r): ∀ _: α, r := fun _ => hr
    ⟨mp, mpr⟩

  example: (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    have mp (pxr: ∀ x, p x ∨ r): (∀ x, p x) ∨ r :=
      sorry
    have mpr: (∀ x, p x) ∨ r → (∀ x, p x ∨ r)
      | .inl px => fun x => .inl (px x)
      | .inr hr => fun _ => .inr hr
    ⟨mp, mpr⟩

  example: (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    have mp (hrpx: ∀ x, r → p x): (r → ∀ x, p x) :=
      fun r x => hrpx x r
    have mpr (hrpx: r → ∀ x, p x): (∀ x, r → p x) :=
      fun x r => hrpx r x
    ⟨mp, mpr⟩
end ExerciseTwo

/-
## 3
-/

section ExerciseThree
  variable (men: Type) (barber: men)
  variable (shaves: men → men → Prop)

  example (h: ∀ x: men, shaves barber x ↔ ¬ shaves x x): False :=
    sorry
end ExerciseThree

/-
## 4
-/

section ExerciseFour
  def even (n₁: Nat): Prop := ∃ n₂: Nat, n₁ = 2 * n₂

  def prime (n: Nat): Prop := sorry

  def infinitely_many_primes : Prop := sorry

  def Fermat_prime (n : Nat) : Prop := sorry

  def infinitely_many_Fermat_primes : Prop := sorry

  def goldbach_conjecture : Prop := sorry

  def Goldbach's_weak_conjecture : Prop := sorry

  def Fermat's_last_theorem : Prop := sorry
end ExerciseFour

end QuantifiersAndEquality
