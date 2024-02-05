/-
# More on the Simply-Typed Lambda Calculus
-/

namespace SoftwareFoundations.ProgrammingLanguageFoundations.MoreStlc
  /-
  ## Simple Extensions to the STLC
  -/

  /- ### Numbers -/
  /- ### Let Bindings -/
  /- ### Pairs -/
  /- ### Unit -/
  /- ### Sums -/
  /- ### Lists -/
  /- ### General Recursion -/
  /- ### Records -/
  /- #### Encoding Records -/
  /- #### Variants -/

  /-
  ## Exercise: Formalizing the Extensions
  -/

  inductive Ty: Type where
    | unit: Ty
    | bool: Ty
    | nat: Ty
    | sum (l r: Ty): Ty
    | prod (l r: Ty): Ty
    | list (e: Ty): Ty
    | arrow (f x: Ty): Ty
  deriving Repr

  section
    declare_syntax_cat stlc_ty

    syntax:max "𝔹" : stlc_ty
    syntax:max "ℕ" : stlc_ty
    syntax:max "‹" term "›" : stlc_ty

    syntax:50 stlc_ty:50 "×" stlc_ty:51 : stlc_ty
    syntax:50 stlc_ty:50 "+" stlc_ty:51 : stlc_ty
    syntax:50 "[" stlc_ty "]" : stlc_ty

    syntax:20 stlc_ty:21 "→" stlc_ty:20 : stlc_ty

    syntax "(" stlc_ty ")" : stlc_ty

    syntax "[Ty|" stlc_ty "]" : term

    macro_rules
      | `([Ty| 𝔹])          => `(Ty.bool)
      | `([Ty| ℕ])          => `(Ty.nat)
      | `([Ty| ‹$ty:term›]) => `($(Lean.quote ty))
      | `([Ty| $t₁ × $t₂])  => `(Ty.prod [Ty| $t₁] [Ty| $t₂])
      | `([Ty| $t₁ + $t₂])  => `(Ty.sum [Ty| $t₁] [Ty| $t₂])
      | `([Ty| [ $t ]])     => `(Ty.list [Ty| $t])
      | `([Ty| $t₁ → $t₂])  => `(Ty.arrow [Ty| $t₁] [Ty| $t₂])
      | `([Ty| ( $ty )])    => `([Ty| $ty])
  end

  section
    example: [Ty| 𝔹] = Ty.bool := rfl
    example: [Ty| ℕ] = Ty.nat := rfl
    example {t:Ty}: [Ty| ‹t›] = t := rfl

    example: [Ty| ℕ × ℕ] = Ty.prod .nat .nat := rfl
    example: [Ty| ℕ × ℕ × ℕ] = Ty.prod (.prod .nat .nat) .nat := rfl
    example: [Ty| ℕ × (ℕ × ℕ)] = Ty.prod .nat (.prod .nat .nat) := rfl

    example: [Ty| ℕ + ℕ] = Ty.sum .nat .nat := rfl
    example: [Ty| ℕ + ℕ + ℕ] = Ty.sum (.sum .nat .nat) .nat := rfl
    example: [Ty| ℕ + (ℕ + ℕ)] = Ty.sum .nat (.sum .nat .nat) := rfl

    example: [Ty| ℕ → ℕ] = Ty.arrow .nat .nat := rfl
    example: [Ty| ℕ → ℕ → ℕ] = Ty.arrow .nat (.arrow .nat .nat) := rfl
    example: [Ty| (ℕ → ℕ) → ℕ] = Ty.arrow (.arrow .nat .nat) .nat := rfl

    example: [Ty| [𝔹]] = Ty.list .bool := rfl

    example: [Ty| ℕ + 𝔹 → ℕ × 𝔹 → [ℕ]] = Ty.arrow (.sum .nat .bool) (.arrow (.prod .nat .bool) (.list .nat)) := rfl
  end

  inductive Term: Type where
    | var (id: String): Term
    | abs (arg: String) (ty: Ty) (b: Term): Term
    | app (f x: Term): Term

    | true: Term
    | false: Term
    | and (t₁ t₂: Term): Term
    | or (t₁ t₂: Term): Term
    | not (t: Term): Term
    | bcase (c t f: Term): Term

    | const (n: Nat): Term
    | pred (t: Term): Term
    | succ (t: Term): Term
    | add (t₁ t₂: Term): Term
    | sub (t₁ t₂: Term): Term
    | mul (t₁ t₂: Term): Term
    | div (t₁ t₂: Term): Term
    | mod (t₁ t₂: Term): Term
    | exp (t₁ t₂: Term): Term

    | eq (t₁ t₂: Term): Term
    | neq (t₁ t₂: Term): Term
    | lt (t₁ t₂: Term): Term
    | le (t₁ t₂: Term): Term
    | gt (t₁ t₂: Term): Term
    | ge (t₁ t₂: Term): Term

    | ite (c t f: Term): Term

    | inl (ty: Ty) (t: Term): Term
    | inr (ty: Ty) (t: Term): Term
    | scase (s: Term) (p₁: String) (b₁: Term) (id₂: String) (b₂: Term): Term

    | nil: Term
    | cons (hd tl: Term): Term
    | lcase (l: Term) (b₁: Term) (hd tl: String) (b₂: Term): Term

    | unit: Term

    | pair (l r: Term): Term
    | fst (p: Term): Term
    | snd (p: Term): Term
    | pcase (p: Term) (id₁ id₂: String) (b: Term): Term

    | let (id: String) (t₁ t₂: Term): Term

    | fix (f: Term): Term
  deriving Repr

  @[reducible]
  def Term.ofBool: Bool → Term
    | .true => .true
    | .false => .false

  section
    declare_syntax_cat stlc

    syntax "(" stlc ")" : stlc
    syntax:max "‹" term "›" : stlc

    syntax:max ident : stlc
    syntax:max "‹id:" term "›" : stlc
    syntax:25 "λ" ident ":" stlc_ty "." stlc : stlc
    syntax:25 "λ" "‹" term "›" ":" stlc_ty "." stlc : stlc
    syntax:85 stlc:85 stlc:86 : stlc

    syntax:max "tru" : stlc
    syntax:max "fls" : stlc
    syntax:max "‹bool:" term "›" : stlc
    syntax:35 stlc:35 "∧" stlc:36 : stlc
    syntax:30 stlc:30 "∨" stlc:31 : stlc
    syntax:max "¬" stlc:95 : stlc
    syntax "case" stlc "of" "|" "tru" "⇒" stlc "|" "fls" "⇒" stlc : stlc

    syntax:max num : stlc
    syntax:max "‹nat:" term "›" : stlc
    syntax:85 "succ" stlc:84 : stlc
    syntax:85 "pred" stlc:84 : stlc
    syntax:65 stlc:65 "+" stlc:66 : stlc
    syntax:65 stlc:65 "-" stlc:66 : stlc
    syntax:70 stlc:70 "*" stlc:71 : stlc
    syntax:70 stlc:70 "/" stlc:71 : stlc
    syntax:70 stlc:70 "%" stlc:71 : stlc
    syntax:80 stlc:81 "^" stlc:80 : stlc

    syntax:50 stlc:50 "=" stlc:50 : stlc
    syntax:50 stlc:50 "≠" stlc:50 : stlc
    syntax:50 stlc:50 "≤" stlc:50 : stlc
    syntax:50 stlc:50 "<" stlc:50 : stlc
    syntax:50 stlc:50 "≥" stlc:50 : stlc
    syntax:50 stlc:50 ">" stlc:50 : stlc

    syntax "ite" stlc "then" stlc "else" stlc : stlc

    syntax "inl" stlc ":" stlc_ty : stlc
    syntax "inr" stlc ":" stlc_ty : stlc
    syntax "case" stlc "of" "|" "inl" ident "⇒" stlc "|" "inr" ident "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "inl" ident "⇒" stlc "|" "inr" "‹" term "›" "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "inl" "‹" term "›" "⇒" stlc "|" "inr" ident "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "inl" "‹" term "›" "⇒" stlc "|" "inr" "‹" term "›" "⇒" stlc : stlc

    syntax:max "[]" : stlc
    syntax:65 stlc:66 "::" stlc:65 : stlc
    syntax "[" stlc,* "]" : stlc
    syntax "case" stlc "of" "|" "nil" "⇒" stlc "|" ident "::" ident "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "nil" "⇒" stlc "|" ident "::" "‹" term "›" "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "nil" "⇒" stlc "|" "‹" term "›" "::" ident "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "nil" "⇒" stlc "|" "‹" term "›" "::" "‹" term "›" "⇒" stlc : stlc

    syntax:max "()" : stlc

    syntax "(" stlc "," stlc ")" : stlc
    syntax:85 "fst" stlc:84 : stlc
    syntax:85 "snd" stlc:84 : stlc
    syntax "case" stlc "of" "|" "(" ident "," ident ")" "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "(" ident "," "‹" term "›" ")" "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "(" "‹" term "›" "," ident ")" "⇒" stlc : stlc
    syntax "case" stlc "of" "|" "(" "‹" term "›" "," "‹" term "›" ")" "⇒" stlc : stlc

    syntax:20 "let" ident "=" stlc "in" stlc : stlc
    syntax:20 "let" "‹" term "›" "=" stlc "in" stlc : stlc

    syntax:60 "fix" stlc:60 : stlc

    syntax "[Term|" stlc "]" : term

    macro_rules
      | `([Term| ( $t )])                                                         => `([Term| $t])
      | `([Term| ‹ $t:term ›])                                                    => `($(Lean.quote t))

      | `([Term| $id:ident])                                                      => `(Term.var $(Lean.quote (toString id.getId)))
      | `([Term| ‹id: $id:term ›])                                                => `(Term.var $(Lean.quote id))
      | `([Term| λ $id : $ty . $t])                                               => `(Term.abs $(Lean.quote (toString id.getId)) [Ty| $ty] [Term| $t])
      | `([Term| λ ‹ $id:term › : $ty . $t])                                      => `(Term.abs $(Lean.quote id) [Ty| $ty] [Term| $t])
      | `([Term| $t₁ $t₂])                                                        => `(Term.app [Term| $t₁] [Term| $t₂])

      | `([Term| tru])                                                            => `(Term.true)
      | `([Term| fls])                                                            => `(Term.false)
      | `([Term| ‹bool: $b:term ›])                                               => `(Term.ofBool $(Lean.quote b))
      | `([Term| $t₁ ∧ $t₂])                                                      => `(Term.and [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ ∨ $t₂])                                                      => `(Term.or [Term| $t₁] [Term| $t₂])
      | `([Term| ¬ $t])                                                           => `(Term.not [Term| $t])
      | `([Term| case $c of | tru ⇒ $t | fls ⇒ $f])                               => `(Term.bcase [Term| $c] [Term| $t] [Term| $f])

      | `([Term| $n:num])                                                         => `(Term.const $n)
      | `([Term| ‹nat: $n:term ›])                                                => `(Term.const $(Lean.quote n))
      | `([Term| succ $t])                                                        => `(Term.succ [Term| $t])
      | `([Term| pred $t])                                                        => `(Term.pred [Term| $t])
      | `([Term| $t₁ + $t₂])                                                      => `(Term.add [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ - $t₂])                                                      => `(Term.sub [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ * $t₂])                                                      => `(Term.mul [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ / $t₂])                                                      => `(Term.div [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ % $t₂])                                                      => `(Term.mod [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ ^ $t₂])                                                      => `(Term.exp [Term| $t₁] [Term| $t₂])

      | `([Term| $t₁ = $t₂])                                                      => `(Term.eq [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ ≠ $t₂])                                                      => `(Term.neq [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ < $t₂])                                                      => `(Term.lt [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ ≤ $t₂])                                                      => `(Term.le [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ > $t₂])                                                      => `(Term.gt [Term| $t₁] [Term| $t₂])
      | `([Term| $t₁ ≥ $t₂])                                                      => `(Term.ge [Term| $t₁] [Term| $t₂])

      | `([Term| ite $c then $t else $f])                                         => `(Term.ite [Term| $c] [Term| $t] [Term| $f])

      | `([Term| inl $t : $ty])                                                   => `(Term.inl [Ty| $ty] [Term| $t])
      | `([Term| inr $t : $ty])                                                   => `(Term.inr [Ty| $ty] [Term| $t])
      | `([Term| case $s of | inl $id₁ ⇒ $t₁ | inr $id₂ ⇒ $t₂])                   => `(Term.scase [Term| $s] $(Lean.quote (toString (id₁).getId)) [Term| $t₁] $(Lean.quote (toString (id₂).getId)) [Term| $t₂])
      | `([Term| case $s of | inl $id₁ ⇒ $t₁ | inr ‹ $id₂:term › ⇒ $t₂])          => `(Term.scase [Term| $s] $(Lean.quote (toString (id₁).getId)) [Term| $t₁] $(Lean.quote id₂) [Term| $t₂])
      | `([Term| case $s of | inl ‹ $id₁:term › ⇒ $t₁ | inr $id₂ ⇒ $t₂])          => `(Term.scase [Term| $s] $(Lean.quote id₁) [Term| $t₁] $(Lean.quote (toString (id₂).getId)) [Term| $t₂])
      | `([Term| case $s of | inl ‹ $id₁:term › ⇒ $t₁ | inr ‹ $id₂:term › ⇒ $t₂]) => `(Term.scase [Term| $s] $(Lean.quote id₁) [Term| $t₁] $(Lean.quote id₂) [Term| $t₂])

      | `([Term| $hd :: $tl])                                                     => `(Term.cons [Term| $hd] [Term| $tl])
      | `([Term| [] ])                                                            => `(Term.nil)
      | `([Term| [ $hd ] ])                                                       => `(Term.cons [Term| $hd] .nil)
      | `([Term| [ $hd , $tl:stlc,* ] ])                                          => `(Term.cons [Term| $hd] [Term| [ $tl,* ]])
      | `([Term| case $l of | nil ⇒ $t₁ | $hd :: $tl ⇒ $t₂])                      => `(Term.lcase [Term| $l] [Term| $t₁] $(Lean.quote (toString hd.getId)) $(Lean.quote (toString tl.getId)) [Term| $t₂])
      | `([Term| case $l of | nil ⇒ $t₁ | $hd :: ‹ $tl › ⇒ $t₂])                  => `(Term.lcase [Term| $l] [Term| $t₁] $(Lean.quote (toString hd.getId)) $(Lean.quote tl) [Term| $t₂])
      | `([Term| case $l of | nil ⇒ $t₁ | ‹ $hd › :: $tl ⇒ $t₂])                  => `(Term.lcase [Term| $l] [Term| $t₁] $(Lean.quote hd) $(Lean.quote (toString tl.getId)) [Term| $t₂])
      | `([Term| case $l of | nil ⇒ $t₁ | ‹ $hd › :: ‹ $tl › ⇒ $t₂])              => `(Term.lcase [Term| $l] [Term| $t₁] $(Lean.quote hd) $(Lean.quote tl) [Term| $t₂])

      | `([Term| () ])                                                            => `(Term.unit)

      | `([Term| ( $t₁ , $t₂ )])                                                  => `(Term.pair [Term| $t₁] [Term| $t₂])
      | `([Term| fst $t])                                                         => `(Term.fst [Term| $t])
      | `([Term| snd $t])                                                         => `(Term.snd [Term| $t])
      | `([Term| case $p of | ( $f , $s ) ⇒ $t])                                  => `(Term.pcase [Term| $p] $(Lean.quote (toString f.getId)) $(Lean.quote (toString s.getId)) [Term| $t])
      | `([Term| case $p of | ( $f , ‹ $s › ) ⇒ $t])                              => `(Term.pcase [Term| $p] $(Lean.quote (toString f.getId)) $(Lean.quote s) [Term| $t])
      | `([Term| case $p of | ( ‹ $f › , $s ) ⇒ $t])                              => `(Term.pcase [Term| $p] $(Lean.quote f) $(Lean.quote (toString s.getId)) [Term| $t])
      | `([Term| case $p of | ( ‹ $f › , ‹ $s › ) ⇒ $t])                          => `(Term.pcase [Term| $p] $(Lean.quote f) $(Lean.quote s) [Term| $t])

      | `([Term| let $id = $t₁ in $t₂])                                           => `(Term.let $(Lean.quote (toString id.getId)) [Term| $t₁] [Term| $t₂])
      | `([Term| let ‹ $id:term › = $t₁ in $t₂])                                  => `(Term.let $(Lean.quote id) [Term| $t₁] [Term| $t₂])

      | `([Term| fix $t])                                                         => `(Term.fix [Term| $t])
  end

  section
    variable {id id₁ id₂: String}
    variable {n: Nat}
    variable {b: Bool}
    variable {c c₁ c₂ t t₁ t₂ t₃ t₄ t₅ t₆ t₇ f f₁ f₂: Term}
    variable {ty ty₁ ty₂: Ty}

    example: [Term| ‹t›] = t := rfl
    example: [Term| (‹t›)] = t := rfl

    example: [Term| foo] = Term.var "foo" := rfl
    example: [Term| ‹id:id›] = Term.var id := rfl
    example: [Term| λ x: 𝔹. y] = Term.abs "x" .bool (.var "y") := rfl
    example: [Term| λ ‹id›: 𝔹. y] = Term.abs id .bool (.var "y") := rfl
    example: [Term| λ f: ℕ → ℕ. λ x: ℕ. f x] = Term.abs "f" (.arrow .nat .nat) (.abs "x" .nat (.app (.var "f") (.var "x"))) := rfl
    example: [Term| f x] = Term.app (.var "f") (.var "x") := rfl
    example: [Term| f x y z] = Term.app (.app (.app (.var "f") (.var "x")) (.var "y")) (.var "z") := rfl

    example: [Term| tru] = Term.true := rfl
    example: [Term| fls] = Term.false := rfl
    example: [Term| ‹bool:true›] = Term.true := rfl
    example: [Term| ‹bool:false›] = Term.false := rfl
    example: [Term| ‹t₁› ∧ ‹t₂›] = Term.and t₁ t₂ := rfl
    example: [Term| ‹t₁› ∧ ‹t₂› ∧ ‹t₃›] = Term.and (.and t₁ t₂) t₃ := rfl
    example: [Term| ‹t₁› ∧ (‹t₂› ∧ ‹t₃›)] = Term.and t₁ (.and t₂ t₃) := rfl
    example: [Term| ‹t₁› ∨ ‹t₂›] = Term.or t₁ t₂ := rfl
    example: [Term| ‹t₁› ∨ ‹t₂› ∨ ‹t₃›] = Term.or (.or t₁ t₂) t₃ := rfl
    example: [Term| ‹t₁› ∨ (‹t₂› ∨ ‹t₃›)] = Term.or t₁ (.or t₂ t₃) := rfl
    example: [Term| ‹t₁› ∧ ‹t₂› ∨ ‹t₃› ∧ ‹t₄›] = Term.or (.and t₁ t₂) (.and t₃ t₄) := rfl
    example: [Term| ¬ ‹t›] = Term.not t := rfl
    example: [Term| ¬ ‹t₁› ∧ ‹t₂›] = Term.and (.not t₁) t₂ := rfl
    example: [Term| ‹t₁› ∨ ¬ ‹t₂›] = Term.or t₁ (.not t₂) := rfl
    example: [Term| case ‹c› of | tru ⇒ ‹t› | fls ⇒ ‹f›] = Term.bcase c t f := rfl

    example: [Term| 42] = Term.const 42 := rfl
    example: [Term| ‹nat:n›] = Term.const n := rfl
    example: [Term| succ ‹t›] = Term.succ t := rfl
    example: [Term| succ succ ‹t›] = Term.succ (.succ t) := rfl
    example: [Term| pred ‹t›] = Term.pred t := rfl
    example: [Term| pred pred ‹t›] = Term.pred (.pred t) := rfl
    example: [Term| pred succ ‹t›] = Term.pred (.succ t) := rfl
    example: [Term| succ pred ‹t›] = Term.succ (.pred t) := rfl
    example: [Term| ‹t₁› + ‹t₂›] = Term.add t₁ t₂ := rfl
    example: [Term| ‹t₁› + ‹t₂› + ‹t₃›] = Term.add (.add t₁ t₂) t₃ := rfl
    example: [Term| ‹t₁› + (‹t₂› + ‹t₃›)] = Term.add t₁ (.add t₂ t₃) := rfl
    example: [Term| succ ‹t₁› + succ ‹t₂›] = Term.add (.succ t₁) (.succ t₂) := rfl
    example: [Term| pred ‹t₁› + pred ‹t₂›] = Term.add (.pred t₁) (.pred t₂) := rfl
    example: [Term| succ pred ‹t₁› + pred succ ‹t₂›] = Term.add (.succ (.pred t₁)) (.pred (.succ t₂)) := rfl
    example: [Term| ‹t₁› - ‹t₂›] = Term.sub t₁ t₂ := rfl
    example: [Term| ‹t₁› - ‹t₂› - ‹t₃›] = Term.sub (.sub t₁ t₂) t₃ := rfl
    example: [Term| ‹t₁› - (‹t₂› - ‹t₃›)] = Term.sub t₁ (.sub t₂ t₃) := rfl
    example: [Term| succ ‹t₁› - succ ‹t₂›] = Term.sub (.succ t₁) (.succ t₂) := rfl
    example: [Term| pred ‹t₁› - pred ‹t₂›] = Term.sub (.pred t₁) (.pred t₂) := rfl
    example: [Term| succ pred ‹t₁› - pred succ ‹t₂›] = Term.sub (.succ (.pred t₁)) (.pred (.succ t₂)) := rfl
    example: [Term| ‹t₁› * ‹t₂›] = Term.mul t₁ t₂ := rfl
    example: [Term| ‹t₁› * ‹t₂› * ‹t₃›] = Term.mul (.mul t₁ t₂) t₃ := rfl
    example: [Term| ‹t₁› * (‹t₂› * ‹t₃›)] = Term.mul t₁ (.mul t₂ t₃) := rfl
    example: [Term| succ ‹t₁› * succ ‹t₂›] = Term.mul (.succ t₁) (.succ t₂) := rfl
    example: [Term| pred ‹t₁› * pred ‹t₂›] = Term.mul (.pred t₁) (.pred t₂) := rfl
    example: [Term| succ pred ‹t₁› * pred succ ‹t₂›] = Term.mul (.succ (.pred t₁)) (.pred (.succ t₂)) := rfl
    example: [Term| ‹t₁› / ‹t₂›] = Term.div t₁ t₂ := rfl
    example: [Term| ‹t₁› / ‹t₂› / ‹t₃›] = Term.div (.div t₁ t₂) t₃ := rfl
    example: [Term| ‹t₁› / (‹t₂› / ‹t₃›)] = Term.div t₁ (.div t₂ t₃) := rfl
    example: [Term| succ ‹t₁› / succ ‹t₂›] = Term.div (.succ t₁) (.succ t₂) := rfl
    example: [Term| pred ‹t₁› / pred ‹t₂›] = Term.div (.pred t₁) (.pred t₂) := rfl
    example: [Term| succ pred ‹t₁› / pred succ ‹t₂›] = Term.div (.succ (.pred t₁)) (.pred (.succ t₂)) := rfl
    example: [Term| ‹t₁› % ‹t₂›] = Term.mod t₁ t₂ := rfl
    example: [Term| ‹t₁› % ‹t₂› % ‹t₃›] = Term.mod (.mod t₁ t₂) t₃ := rfl
    example: [Term| ‹t₁› % (‹t₂› % ‹t₃›)] = Term.mod t₁ (.mod t₂ t₃) := rfl
    example: [Term| succ ‹t₁› % succ ‹t₂›] = Term.mod (.succ t₁) (.succ t₂) := rfl
    example: [Term| pred ‹t₁› % pred ‹t₂›] = Term.mod (.pred t₁) (.pred t₂) := rfl
    example: [Term| succ pred ‹t₁› % pred succ ‹t₂›] = Term.mod (.succ (.pred t₁)) (.pred (.succ t₂)) := rfl
    example: [Term| ‹t₁› ^ ‹t₂›] = Term.exp t₁ t₂ := rfl
    example: [Term| ‹t₁› ^ ‹t₂› ^ ‹t₃›] = Term.exp t₁ (.exp t₂ t₃) := rfl
    example: [Term| (‹t₁› ^ ‹t₂›) ^ ‹t₃›] = Term.exp (.exp t₁ t₂) t₃ := rfl
    example: [Term| succ ‹t₁› ^ succ ‹t₂›] = Term.exp (.succ t₁) (.succ t₂) := rfl
    example: [Term| pred ‹t₁› ^ pred ‹t₂›] = Term.exp (.pred t₁) (.pred t₂) := rfl
    example: [Term| succ pred ‹t₁› ^ pred succ ‹t₂›] = Term.exp (.succ (.pred t₁)) (.pred (.succ t₂)) := rfl
    -- example: [Term| ‹t₁› + ‹t₂› - ‹t₃›] = Term.add t₁ (.sub t₂ t₃) := rfl
    -- example: [Term| ‹t₁› - ‹t₂› + ‹t₃›] = Term.sub t₁ (.add t₂ t₃) := rfl
    -- example: [Term| ‹t₁› * ‹t₂› / ‹t₃›] = Term.mul t₁ (.div t₂ t₃) := rfl
    -- example: [Term| ‹t₁› / ‹t₂› * ‹t₃›] = Term.div t₁ (.mul t₂ t₃) := rfl
    -- example: [Term| ‹t₁› * ‹t₂› % ‹t₃›] = Term.mul t₁ (.div t₂ t₃) := rfl
    -- example: [Term| ‹t₁› * ‹t₂› + ‹t₃› * ‹t₄›] = Term.add (.mul t₁ t₂) (.mul t₃ t₄) := rfl
    -- example: [Term| pred ‹t₁› * succ ‹t₂› + f ‹t₃› / ‹t₄› - ‹t₅› % ‹t₆› ^ ‹t₇›] =
    --   Term.add
    --     (.mul
    --       (.pred t₁)
    --       (.succ t₂))
    --     (Term.sub
    --       (.div
    --         (.app (.var "f") t₃)
    --         t₄)
    --       (.mod
    --         t₅
    --         (.exp t₆ t₇))) := rfl
    -- Term.sub
    --   (Term.add
    --     (Term.mul
    --       (Term.pred t₁)
    --       (Term.succ t₂))
    --     (Term.div
    --       (Term.app (Term.var "f") t₃)
    --       t₄))
    --   (Term.mod
    --     t₅
    --     (Term.exp t₆ t₇))

    example: [Term| ‹t₁› = ‹t₂›] = Term.eq t₁ t₂ := rfl
    example: [Term| ‹t₁› ≠ ‹t₂›] = Term.neq t₁ t₂ := rfl
    example: [Term| ‹t₁› < ‹t₂›] = Term.lt t₁ t₂ := rfl
    example: [Term| ‹t₁› ≤ ‹t₂›] = Term.le t₁ t₂ := rfl
    example: [Term| ‹t₁› > ‹t₂›] = Term.gt t₁ t₂ := rfl
    example: [Term| ‹t₁› ≥ ‹t₂›] = Term.ge t₁ t₂ := rfl

    example: [Term| ‹t₁› + ‹t₂› = ‹t₃› ^ ‹t₄›] = Term.eq (.add t₁ t₂) (.exp t₃ t₄) := rfl
    example: [Term| ‹t₁› + ‹t₂› ≠ ‹t₃› ^ ‹t₄›] = Term.neq (.add t₁ t₂) (.exp t₃ t₄) := rfl
    example: [Term| ‹t₁› + ‹t₂› < ‹t₃› ^ ‹t₄›] = Term.lt (.add t₁ t₂) (.exp t₃ t₄) := rfl
    example: [Term| ‹t₁› + ‹t₂› ≤ ‹t₃› ^ ‹t₄›] = Term.le (.add t₁ t₂) (.exp t₃ t₄) := rfl
    example: [Term| ‹t₁› + ‹t₂› > ‹t₃› ^ ‹t₄›] = Term.gt (.add t₁ t₂) (.exp t₃ t₄) := rfl
    example: [Term| ‹t₁› + ‹t₂› ≥ ‹t₃› ^ ‹t₄›] = Term.ge (.add t₁ t₂) (.exp t₃ t₄) := rfl

    example: [Term| ‹t₁› = ‹t₂› ∧ ‹t₃› ≠ ‹t₄›] = Term.and (.eq t₁ t₂) (.neq t₃ t₄) := rfl
    example: [Term| ‹t₁› = ‹t₂› ∨ ‹t₃› ≠ ‹t₄›] = Term.or (.eq t₁ t₂) (.neq t₃ t₄) := rfl
    example: [Term| ¬‹t₁› = ‹t₂› ∧ ‹t₃› ≠ ‹t₄›] = Term.and (.eq (.not t₁) t₂) (.neq t₃ t₄) := rfl
    example: [Term| ¬(‹t₁› = ‹t₂›) ∧ ‹t₃› ≠ ‹t₄›] = Term.and (.not (.eq t₁ t₂)) (.neq t₃ t₄) := rfl

    example: [Term| ite ‹c› then ‹t› else ‹f›] = Term.ite c t f := rfl
    example: [Term| ite ‹c› ‹t₁› ‹t₂› then ‹t› ‹t₃› ‹t₄› else ‹f› ‹t₅› ‹t₆›] = Term.ite (.app (.app c t₁) t₂) (.app (.app t t₃) t₄) (.app (.app f t₅) t₆) := rfl
    example: [Term| ite ‹t₁› ∧ ‹t₂› then ‹t₃› ∨ ‹t₄› else ‹t₅› ≠ ‹t₆›] = Term.ite (.and t₁ t₂) (.or t₃ t₄) (.neq t₅ t₆) := rfl

    example: [Term| inl 42: ℕ] = Term.inl .nat (.const 42) := rfl
    example: [Term| inr tru: 𝔹] = Term.inr .bool .true := rfl
    example: [Term| inl 1 + 2: ℕ ∧ inr ¬ tru: 𝔹] = Term.and (.inl .nat (.add (.const 1) (.const 2))) (.inr .bool (.not .true)) := rfl
    example: [Term| inl 1 + 2: ℕ ≠ inr ¬ tru: 𝔹] = Term.neq (.inl .nat (.add (.const 1) (.const 2))) (.inr .bool (.not .true)) := rfl
    example: [Term| case ‹t₁› of | inl x ⇒ ‹t₂› | inr y ⇒ ‹t₃›] = Term.scase t₁ "x" t₂ "y" t₃ := rfl
    example: [Term| case ‹t₁› of | inl ‹id₁› ⇒ ‹t₂› | inr y ⇒ ‹t₃›] = Term.scase t₁ id₁ t₂ "y" t₃ := rfl
    example: [Term| case ‹t₁› of | inl x ⇒ ‹t₂› | inr ‹id₂› ⇒ ‹t₃›] = Term.scase t₁ "x" t₂ id₂ t₃ := rfl
    example: [Term| case ‹t₁› of | inl ‹id₁› ⇒ ‹t₂› | inr ‹id₂› ⇒ ‹t₃›] = Term.scase t₁ id₁ t₂ id₂ t₃ := rfl
    example: [Term| case ‹t₁› of | inl ‹id₁› ⇒ ‹t₂› ∧ ‹t₃› * ‹t₄› | inr ‹id₂› ⇒ ‹t₅› ∨ ‹t₆›] = Term.scase t₁ id₁ (.and t₂ (.mul t₃ t₄)) id₂ (.or t₅ t₆) := rfl

    example: [Term| []] = Term.nil := rfl
    example: [Term| ‹t₁› :: ‹t₂›] = Term.cons t₁ t₂ := rfl
    example: [Term| ‹t₁› :: ‹t₂› :: ‹t₃›] = Term.cons t₁ (.cons t₂ t₃) := rfl
    example: [Term| (‹t₁› :: ‹t₂›) :: ‹t₃›] = Term.cons (.cons t₁ t₂) t₃ := rfl
    example: [Term| [‹t₁›]] = Term.cons t₁ .nil := rfl
    example: [Term| [‹t₁›, ‹t₂›]] = Term.cons t₁ (.cons t₂ .nil) := rfl
    example: [Term| [‹t₁›, ‹t₂›, ‹t₃›]] = Term.cons t₁ (.cons t₂ (.cons t₃ .nil)) := rfl
    example: [Term| ‹t₁› :: []] = Term.cons t₁ .nil := rfl
    example: [Term| [‹t₁› ∧ ‹t₂›, ‹t₃› ^ ‹t₄›]] = Term.cons (.and t₁ t₂) (.cons (.exp t₃ t₄) .nil) := rfl
    example: [Term| (‹t₁› ∧ ‹t₂›) :: ‹t₄›] = Term.cons (.and t₁ t₂) t₄ := rfl
    example: [Term| ‹t₁› * ‹t₂› :: ‹t₄›] = Term.cons (.mul t₁ t₂) t₄ := rfl
    example: [Term| ‹t₁› ‹t₂› :: ‹t₄›] = Term.cons (.app t₁ t₂) t₄ := rfl
    example: [Term| case ‹t₁› of | nil ⇒ ‹t₂› | hd::tl ⇒ ‹t₃›] = Term.lcase t₁ t₂ "hd" "tl" t₃ := rfl
    example: [Term| case ‹t₁› of | nil ⇒ ‹t₂› | hd::‹id₂› ⇒ ‹t₃›] = Term.lcase t₁ t₂ "hd" id₂ t₃ := rfl
    example: [Term| case ‹t₁› of | nil ⇒ ‹t₂› | ‹id₁›::tl ⇒ ‹t₃›] = Term.lcase t₁ t₂ id₁ "tl" t₃ := rfl
    example: [Term| case ‹t₁› of | nil ⇒ ‹t₂› | ‹id₁›::‹id₂› ⇒ ‹t₃›] = Term.lcase t₁ t₂ id₁ id₂ t₃ := rfl

    example: [Term| ()] = Term.unit := rfl

    example: [Term| (tru, 42)] = Term.pair .true (.const 42) := rfl
    example: [Term| fst ‹t₁›] = Term.fst t₁ := rfl
    example: [Term| snd ‹t₁›] = Term.snd t₁ := rfl
    example: [Term| fst snd ‹t₁›] = Term.fst (.snd t₁) := rfl
    example: [Term| fst ‹t₁› ^ snd ‹t₁›] = Term.exp (.fst t₁) (.snd t₁) := rfl
    example: [Term| case ‹t₁› of | (f, s) ⇒ ‹t₂›] = Term.pcase t₁ "f" "s" t₂ := rfl
    example: [Term| case ‹t₁› of | (f, ‹id₂›) ⇒ ‹t₂›] = Term.pcase t₁ "f" id₂ t₂ := rfl
    example: [Term| case ‹t₁› of | (‹id₁›, s) ⇒ ‹t₂›] = Term.pcase t₁ id₁ "s" t₂ := rfl
    example: [Term| case ‹t₁› of | (‹id₁›, ‹id₂›) ⇒ ‹t₂›] = Term.pcase t₁ id₁ id₂ t₂ := rfl

    example: [Term| let x = ‹t₁› in ‹t₂›] = Term.let "x" t₁ t₂ := rfl
    example: [Term| let x = ‹t₁› ∨ ‹t₂› in ‹t₃›] = Term.let "x" (.or t₁ t₂) t₃ := rfl
    example: [Term| let ‹id₁› = ‹t₁› in ‹t₂›] = Term.let id₁ t₁ t₂ := rfl

    example: [Term| fix ‹t₁›] = Term.fix t₁ := rfl
    example: [Term| fix (λ ‹id₁›: ℕ. ‹t₁›)] = Term.fix (.abs id₁ .nat t₁) := rfl
  end
end SoftwareFoundations.ProgrammingLanguageFoundations.MoreStlc
