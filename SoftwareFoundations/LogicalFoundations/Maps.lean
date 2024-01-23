/-
# Total and Partial Maps
-/

/-
## Identifiers
-/

#check BEq String

/-
## Total Maps
-/

def TotalMap (α: Type): Type := String → α

def TotalMap.empty {α: Type} (default: α): TotalMap α := fun _ => default

def TotalMap.update {α: Type} (m: TotalMap α) (k: String) (v: α): TotalMap α :=
  fun k₁ =>
    if k == k₁
    then v
    else m k₁

example: TotalMap Bool :=
  ((TotalMap.empty false).update "foo" true).update "bar" true

@[simp]
theorem TotalMap.applyEmpty (k: String) (v: α): (TotalMap.empty v) k = v := by rfl

@[simp]
theorem TotalMap.updateEq (m: TotalMap α) (k: String) (v: α): (m.update k v) k = v := by
  unfold TotalMap.update
  simp

@[simp]
theorem TotalMap.updateNeq (m: TotalMap α) (k₁ k₂: String) (v: α) (h: k₁ ≠ k₂): (m.update k₁ v) k₂ = m k₂ := by
  unfold TotalMap.update
  simp_all

@[simp]
theorem TotalMap.updateShadow (m: TotalMap α) (k: String) (v₁ v₂: α): ((m.update k v₁).update k v₂) k = (m.update k v₂) k := by
  unfold TotalMap.update
  simp

@[simp]
theorem TotalMap.updateSame (m: TotalMap α) (k: String): (m.update k (m k)) = m := by
  unfold TotalMap.update
  funext x
  cases k == x with
    | true =>
      simp
      congr
      sorry
    | false => simp

theorem TotalMap.updatePermute (m: TotalMap α) (k₁ k₂: String) (v₁ v₂: α) (h: k₁ ≠ k₂): (m.update k₁ v₁).update k₂ v₂ = (m.update k₂ v₂).update k₁ v₁ := by
  simp at *
  unfold TotalMap.update
  funext x
  cases k₁ == x with
    | true =>
      cases k₂ == x with
        | true => simp; sorry
        | false => simp
    | false =>
      cases k₂ == x with
        | true => simp
        | false => simp

/-
## Partial Maps
-/

def PartialMap (α: Type): Type := TotalMap (Option α)

def PartialMap.empty: PartialMap α := TotalMap.empty .none
def PartialMap.update (m: PartialMap α) (k: String) (v: α): PartialMap α := TotalMap.update m k v
def PartialMap.includes (m₁ m₂: PartialMap α): Prop := ∀ k: String, ∀ v: α, m₁ k = .some v → m₂ k = .some v

theorem PartialMap.applyEmpty (k: String): @PartialMap.empty α k = .none := by rfl

@[simp]
theorem PartialMap.updateEq (m: PartialMap α) (k: String) (v: α): (m.update k v) k = v := by
  unfold PartialMap.update
  rw [TotalMap.updateEq]

@[simp]
theorem PartialMap.updateNeq (m: PartialMap α) (k₁ k₂: String) (v: α) (h: k₁ ≠ k₂): (m.update k₁ v) k₂ = m k₂ := by
  unfold PartialMap.update
  rw [TotalMap.updateNeq]
  assumption

@[simp]
theorem PartialMap.updateShadow (m: PartialMap α) (k: String) (v₁ v₂: α): ((m.update k v₁).update k v₂) k = (m.update k v₂) k := by
  unfold PartialMap.update
  rw [TotalMap.updateShadow]

@[simp]
theorem PartialMap.updateSame (m: PartialMap α) (k: String) (v: α) (h: m k = .some v): (m.update k v) = m := by
  unfold PartialMap.update
  rw [← h]
  rw [TotalMap.updateSame]

theorem PartialMap.updatePermute (m: PartialMap α) (k₁ k₂: String) (v₁ v₂: α) (h: k₁ ≠ k₂): (m.update k₁ v₁).update k₂ v₂ = (m.update k₂ v₂).update k₁ v₁ := by
  unfold PartialMap.update
  rw [TotalMap.updatePermute]
  assumption

theorem PartialMap.includesUpdate (m₁ m₂: PartialMap α) (k: String) (v: α) (h: m₁.includes m₂): (m₁.update k v).includes (m₂.update k v) := by
  unfold PartialMap.includes
  intro k₁ v₁ h₂
  cases k == k₁ with
    | true =>sorry
    | false => sorry
