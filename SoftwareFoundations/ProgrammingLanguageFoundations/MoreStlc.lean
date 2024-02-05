/-
# More on the Simply-Typed Lambda Calculus
-/

import SoftwareFoundations.LogicalFoundations.Maps
import SoftwareFoundations.ProgrammingLanguageFoundations.SmallStep

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

  /-
  #### Syntaxs
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

    syntax:50 "()" : stlc_ty
    syntax:50 stlc_ty:50 "×" stlc_ty:51 : stlc_ty
    syntax:50 stlc_ty:50 "+" stlc_ty:51 : stlc_ty
    syntax:50 "[" stlc_ty "]" : stlc_ty

    syntax:20 stlc_ty:21 "→" stlc_ty:20 : stlc_ty

    syntax "(" stlc_ty ")" : stlc_ty

    syntax "[Ty|" stlc_ty "]" : term

    macro_rules
      | `([Ty| 𝔹])          => `(Ty.bool)
      | `([Ty| ℕ])          => `(Ty.nat)
      | `([Ty| ()])         => `(Ty.unit)
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
    example: [Ty| ()] = Ty.unit := rfl
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

    | inl (t: Term) (ty: Ty): Term
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

    syntax "inl" "(" stlc "|" stlc_ty ")" : stlc
    syntax "inr" "(" stlc_ty "|" stlc ")" : stlc
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

      | `([Term| inl ( $t | $ty )])                                               => `(Term.inl [Term| $t] [Ty| $ty])
      | `([Term| inr ( $ty | $t )])                                               => `(Term.inr [Ty| $ty] [Term| $t])
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

    example: [Term| inl (42 | ℕ)] = Term.inl (.const 42) .nat := rfl
    example: [Term| inr (𝔹 | tru)] = Term.inr .bool .true := rfl
    example: [Term| inl (1 + 2 | ℕ) ∧ inr (𝔹 | ¬ tru)] = Term.and (.inl (.add (.const 1) (.const 2)) .nat) (.inr .bool (.not .true)) := rfl
    example: [Term| inl (1 + 2 | ℕ) ≠ inr (𝔹 | ¬ tru)] = Term.neq (.inl (.add (.const 1) (.const 2)) .nat) (.inr .bool (.not .true)) := rfl
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

  /-
  #### Substitution
  -/

  @[reducible]
  def Term.subst (id: String) (s: Term): Term → Term
    | .var v     => if id = v then s else .var v
    | .abs v t b => if id = v then .abs v t b else .abs v t (subst id s b)
    | .app f x   => .app (subst id s f) (subst id s x)

    | .true        => .true
    | .false       => .false
    | .and t₁ t₂   => .and (subst id s t₁) (subst id s t₂)
    | .or t₁ t₂    => .or (subst id s t₁) (subst id s t₂)
    | .not t       => .not (subst id s t)
    | .bcase c t f => .bcase (subst id s c) (subst id s t) (subst id s f)

    | .const n   => .const n
    | .pred t    => .pred (subst id s t)
    | .succ t    => .succ (subst id s t)
    | .add t₁ t₂ => .add (subst id s t₁) (subst id s t₂)
    | .sub t₁ t₂ => .sub (subst id s t₁) (subst id s t₂)
    | .mul t₁ t₂ => .mul (subst id s t₁) (subst id s t₂)
    | .div t₁ t₂ => .div (subst id s t₁) (subst id s t₂)
    | .mod t₁ t₂ => .mod (subst id s t₁) (subst id s t₂)
    | .exp t₁ t₂ => .exp (subst id s t₁) (subst id s t₂)

    | .eq t₁ t₂  => .eq (subst id s t₁) (subst id s t₂)
    | .neq t₁ t₂ => .neq (subst id s t₁) (subst id s t₂)
    | .lt t₁ t₂  => .lt (subst id s t₁) (subst id s t₂)
    | .le t₁ t₂  => .le (subst id s t₁) (subst id s t₂)
    | .gt t₁ t₂  => .gt (subst id s t₁) (subst id s t₂)
    | .ge t₁ t₂  => .ge (subst id s t₁) (subst id s t₂)

    | .ite c t f => .ite (subst id s c) (subst id s t) (subst id s f)

    | .inl t ty              => .inl (subst id s t) ty
    | .inr ty t              => .inr ty (subst id s t)
    | .scase c id₁ b₁ id₂ b₂ =>
      let b₁ := if id₁ = id then b₁ else subst id s b₁
      let b₂ := if id₂ = id then b₂ else subst id s b₂
      .scase (subst id s c) id₁ b₁ id₂ b₂

    | .nil                 => .nil
    | .cons hd tl          => .cons (subst id s hd) (subst id s tl)
    | .lcase l b₁ hd tl b₂ =>
      let b₂ := if id = hd ∨ id = tl then b₂ else subst id s b₂
      .lcase (subst id s l) (subst id s b₁) hd tl b₂

    | .unit => .unit

    | .pair l r          => .pair (subst id s l) (subst id s r)
    | .fst p             => .fst (subst id s p)
    | .snd p             => .snd (subst id s p)
    | .pcase p id₁ id₂ b =>
      let b := if id = id₁ ∨ id = id₂ then b else subst id s b
      .pcase p id₁ id₂ b

    | .let v t₁ t₂ =>
      if id = v
      then .let v t₁ t₂
      else .let v (subst id s t₁) (subst id s t₂)

    | .fix f => .fix (subst id s f)

  scoped notation "[" id "↦" s "]" t => Term.subst id s t

  section
    example: (["z" ↦ (.const 0)] [Term| (λ x: 𝔹. z)]) = [Term| λ x: 𝔹. 0] := rfl
    example: (["z" ↦ (.const 0)] [Term| (λ z: 𝔹. z)]) = [Term| λ z: 𝔹. z] := rfl

    example: (["z" ↦ (.const 0)] [Term| case tru of | tru ⇒ z | fls ⇒ z]) = [Term| case tru of | tru ⇒ 0 | fls ⇒ 0] := rfl

    example: (["z" ↦ (.const 0)] [Term| case x of | inl l ⇒ z | inr r ⇒ z]) = [Term| case x of | inl l ⇒ 0 | inr r ⇒ 0] := rfl
    example: (["z" ↦ (.const 0)] [Term| case x of | inl l ⇒ z | inr z ⇒ z]) = [Term| case x of | inl l ⇒ 0 | inr z ⇒ z] := rfl
    example: (["z" ↦ (.const 0)] [Term| case x of | inl z ⇒ z | inr r ⇒ z]) = [Term| case x of | inl z ⇒ z | inr r ⇒ 0] := rfl
    example: (["z" ↦ (.const 0)] [Term| case x of | inl z ⇒ z | inr z ⇒ z]) = [Term| case x of | inl z ⇒ z | inr z ⇒ z] := rfl

    example: (["z" ↦ (.const 0)] [Term| case [] of | nil ⇒ z | hd::tl ⇒ z]) = [Term| case [] of | nil ⇒ 0 | hd::tl ⇒ 0] := rfl
    example: (["z" ↦ (.const 0)] [Term| case [] of | nil ⇒ z | hd::z ⇒ z]) = [Term| case [] of | nil ⇒ 0 | hd::z ⇒ z] := rfl
    example: (["z" ↦ (.const 0)] [Term| case [] of | nil ⇒ z | z::tl ⇒ z]) = [Term| case [] of | nil ⇒ 0 | z::tl ⇒ z] := rfl
    example: (["z" ↦ (.const 0)] [Term| case [] of | nil ⇒ z | z::z ⇒ z]) = [Term| case [] of | nil ⇒ 0 | z::z ⇒ z] := rfl

    example: (["z" ↦ (.const 0)] [Term| case (x, y) of | (l, r) ⇒ z]) = [Term| case (x, y) of | (l, r) ⇒ 0] := rfl
    example: (["z" ↦ (.const 0)] [Term| case (x, y) of | (l, z) ⇒ z]) = [Term| case (x, y) of | (l, z) ⇒ z] := rfl
    example: (["z" ↦ (.const 0)] [Term| case (x, y) of | (z, r) ⇒ z]) = [Term| case (x, y) of | (z, r) ⇒ z] := rfl
    example: (["z" ↦ (.const 0)] [Term| case (x, y) of | (z, z) ⇒ z]) = [Term| case (x, y) of | (z, z) ⇒ z] := rfl

    example: (["z" ↦ (.const 0)] [Term| let w = z in z]) = [Term| let w = 0 in 0] := rfl
    example: (["z" ↦ (.const 0)] [Term| let w = z in w]) = [Term| let w = 0 in w] := rfl
    example: (["z" ↦ (.const 0)] [Term| let y = succ 0 in z]) = [Term| let y = succ 0 in 0] := rfl
  end

  inductive Subst (id: String) (s: Term): Term → Term → Prop where

  namespace Term
    theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
  end Term

  namespace Tactic
    theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := by sorry
  end Tactic

  namespace Blended
    theorem Subst.correct {id: String} {s t₁ t₂: Term}: ([id ↦ s] t₁) = t₂ ↔ Subst id s t₁ t₂ := sorry
  end Blended

  /-
  #### Reduction
  -/

  inductive Value: Term → Prop where
    | true: Value [Term| tru]
    | false: Value [Term| fls]
    | const {n: Nat}: Value [Term| ‹nat:n›]
    | abs {id: String} {ty: Ty} {b: Term}: Value [Term| λ ‹id›: ‹ty›. ‹b›]
    | inl {ty: Ty} {t: Term} (h₁: Value t): Value [Term| inl (‹t› | ‹ty›)]
    | inr {ty: Ty} {t: Term} (h₁: Value t): Value [Term| inr (‹ty› | ‹t›)]
    | nil: Value [Term| []]
    | cons {t₁ t₂: Term} (h₁: Value t₁) (h₂: Value t₂): Value [Term| ‹t₁› :: ‹t₂›]
    | unit: Value [Term| ()]
    | pair {t₁ t₂: Term} (h₁: Value t₁) (h₂: Value t₂): Value [Term| (‹t₁›, ‹t₂›)]

  inductive Eq: Term → Term → Prop where
    | true: Eq [Term| tru] [Term| tru]
    | false: Eq [Term| fls] [Term| fls]
    | const {n₁ n₂: Nat} (h₁: n₁ = n₂): Eq [Term| ‹nat:n₁›] [Term| ‹nat:n₂›]
    | inl {t₁ t₂: Term} {ty₁ ty₂: Ty} (h₁: Value t₁) (h₂: Value t₂) (h₃: Eq t₁ t₂) (h₄: ty₁ = ty₂): Eq [Term| inl (‹t₁› | ‹ty₁›)] [Term| inl (‹t₂› | ‹ty₂›)]
    | inr {t₁ t₂: Term} {ty₁ ty₂: Ty} (h₁: Value t₁) (h₂: Value t₂) (h₃: Eq t₁ t₂) (h₄: ty₁ = ty₂): Eq [Term| inr (‹ty₁› | ‹t₁›)] [Term| inr (‹ty₂› | ‹t₂›)]
    | nil: Eq [Term| []] [Term| []]
    | cons {hd₁ hd₂ tl₁ tl₂: Term} (h₁: Value hd₁) (h₂: Value hd₂) (h₃: Value tl₁) (h₄: Value tl₂) (h₅: Eq hd₁ hd₂) (h₆: Eq tl₁ tl₂): Eq [Term| ‹hd₁› :: ‹tl₁›] [Term| ‹hd₂› :: ‹tl₂›]
    | unit: Eq [Term| ()] [Term| ()]
    | pair {f₁ f₂ s₁ s₂: Term} (h₁: Value f₁) (h₂: Value f₂) (h₃: Value s₁) (h₄: Value s₂) (h₅: Eq f₁ f₂) (h₆: Eq s₁ s₂): Eq [Term| (‹f₁›, ‹s₁›)] [Term| (‹f₂›, ‹s₂›)]

  inductive Eval₁: Term → Term → Prop where
    | appL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› ‹t₃›] [Term| ‹t₂› ‹t₃›]
    | appR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› ‹t₁›] [Term| ‹v₁› ‹t₂›]
    | appAbs {id: String} {t: Ty} {b x: Term} (h₁: Value x): Eval₁ [Term| (λ ‹id›: ‹ty›. ‹b›) ‹x›] ([id ↦ x] [Term| ‹b›])

    | andL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› ∧ ‹t₃›] [Term| ‹t₂› ∧ ‹t₃›]
    | andR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› ∧ ‹t₁›] [Term| ‹v₂› ∧ ‹t₂›]
    | andTrueTrue: Eval₁ [Term| tru ∧ tru] [Term| tru]
    | andTrueFalse: Eval₁ [Term| tru ∧ fls] [Term| fls]
    | andFalseTrue: Eval₁ [Term| fls ∧ tru] [Term| fls]
    | andFalseFalse: Eval₁ [Term| fls ∧ fls] [Term| fls]
    | orL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› ∨ ‹t₃›] [Term| ‹t₂› ∨ ‹t₃›]
    | orR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› ∨ ‹t₁›] [Term| ‹v₂› ∨ ‹t₂›]
    | orTrueTrue: Eval₁ [Term| tru ∧ tru] [Term| tru]
    | orTrueFalse: Eval₁ [Term| tru ∧ fls] [Term| tru]
    | orFalseTrue: Eval₁ [Term| fls ∧ tru] [Term| tru]
    | orFalseFalse: Eval₁ [Term| fls ∧ fls] [Term| fls]
    | notStep {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ¬ ‹t₁›] [Term| ¬ ‹t₂›]
    | notTrue: Eval₁ [Term| ¬ tru] [Term| fls]
    | notFalse: Eval₁ [Term| ¬ fls] [Term| tru]
    | bcaseTrue {t f: Term}: Eval₁ [Term| case tru of | tru ⇒ ‹t› | fls ⇒ ‹f›] [Term| ‹t›]
    | bcaseFalse {t f: Term}: Eval₁ [Term| case fls of | tru ⇒ ‹t› | fls ⇒ ‹f›] [Term| ‹f›]
    | bcase {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [Term| case ‹c₁› of | tru ⇒ ‹t› | fls ⇒ ‹f›] [Term| case ‹c₂› of | tru ⇒ ‹t› | fls ⇒ ‹f›]

    | succConst {n: Nat}: Eval₁ [Term| succ ‹nat:n›] [Term| ‹nat:n + 1›]
    | succ {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| succ ‹t₁›] [Term| succ ‹t₂›]
    | predZero: Eval₁ [Term| pred 0] [Term| 0]
    | predSucc {v: Term} (h₁: Value v): Eval₁ [Term| pred succ ‹v›] [Term| ‹v›]
    | pred {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| pred ‹t₁›] [Term| pred ‹t₂›]
    | addL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› + ‹t₃›] [Term| ‹t₂› + ‹t₃›]
    | addR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› + ‹t₁›] [Term| ‹v₁› + ‹t₂›]
    | add {n₁ n₂: Nat}: Eval₁ [Term| ‹nat:n₁› + ‹nat:n₂›] [Term| ‹nat:n₁ + n₂›]
    | subL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› - ‹t₃›] [Term| ‹t₂› - ‹t₃›]
    | subR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› - ‹t₁›] [Term| ‹v₁› - ‹t₂›]
    | sub {n₁ n₂: Nat}: Eval₁ [Term| ‹nat:n₁› - ‹nat:n₂›] [Term| ‹nat:n₁ - n₂›]
    | mulL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› * ‹t₃›] [Term| ‹t₂› * ‹t₃›]
    | mulR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› * ‹t₁›] [Term| ‹v₁› * ‹t₂›]
    | mul {n₁ n₂: Nat}: Eval₁ [Term| ‹nat:n₁› * ‹nat:n₂›] [Term| ‹nat:n₁ * n₂›]
    | divL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› / ‹t₃›] [Term| ‹t₂› / ‹t₃›]
    | divR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› / ‹t₁›] [Term| ‹v₁› / ‹t₂›]
    | div {n₁ n₂: Nat}: Eval₁ [Term| ‹nat:n₁› / ‹nat:n₂›] [Term| ‹nat:n₁ / n₂›]
    | modL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› % ‹t₃›] [Term| ‹t₂› % ‹t₃›]
    | modR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› % ‹t₁›] [Term| ‹v₁› % ‹t₂›]
    | mod {n₁ n₂: Nat}: Eval₁ [Term| ‹nat:n₁› % ‹nat:n₂›] [Term| ‹nat:n₁ % n₂›]
    | expL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› ^ ‹t₃›] [Term| ‹t₂› ^ ‹t₃›]
    | expR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› ^ ‹t₁›] [Term| ‹v₁› ^ ‹t₂›]
    | exp {n₁ n₂: Nat}: Eval₁ [Term| ‹nat:n₁› ^ ‹nat:n₂›] [Term| ‹nat:n₁ ^ n₂›]

    | eqL {t₁ t₃ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› = ‹t₃›] [Term| ‹t₂› = ‹t₃›]
    | eqR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› = ‹t₁›] [Term| ‹v₁› = ‹t₂›]
    | eqTrue {v₁ v₂: Term} (h₁: Value v₁) (h₂: Value v₂) (h₃: Eq v₁ v₂): Eval₁ [Term| ‹v₁› = ‹v₂›] [Term| tru]
    | eqFalse {v₁ v₂: Term} (h₁: Value v₁) (h₂: Value v₂) (h₃: ¬ Eq v₁ v₂): Eval₁ [Term| ‹v₁› = ‹v₂›] [Term| fls]
    | neqL {t₁ t₃ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› ≠ ‹t₃›] [Term| ‹t₂› ≠ ‹t₃›]
    | neqR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› ≠ ‹t₁›] [Term| ‹v₁› ≠ ‹t₂›]
    | neqTrue {v₁ v₂: Term} (h₁: Value v₁) (h₂: Value v₂) (h₃: ¬ Eq v₁ v₂): Eval₁ [Term| ‹v₁› ≠ ‹v₂›] [Term| tru]
    | neqFalse {v₁ v₂: Term} (h₁: Value v₁) (h₂: Value v₂) (h₃: Eq v₁ v₂): Eval₁ [Term| ‹v₁› ≠ ‹v₂›] [Term| fls]
    | ltL {t₁ t₃ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› < ‹t₃›] [Term| ‹t₂› < ‹t₃›]
    | ltR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› < ‹t₁›] [Term| ‹v₁› < ‹t₂›]
    | ltTrue {n₁ n₂: Nat} (h₁: n₁ < n₂): Eval₁ [Term| ‹nat:n₁› < ‹nat:n₂›] [Term| tru]
    | ltFalse {n₁ n₂: Nat} (h₁: n₁ ≥ n₂): Eval₁ [Term| ‹nat:n₁› < ‹nat:n₂›] [Term| fls]
    | leL {t₁ t₃ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› ≤ ‹t₃›] [Term| ‹t₂› ≤ ‹t₃›]
    | leR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› ≤ ‹t₁›] [Term| ‹v₁› ≤ ‹t₂›]
    | leTrue {n₁ n₂: Nat} (h₁: n₁ ≤ n₂): Eval₁ [Term| ‹nat:n₁› ≤ ‹nat:n₂›] [Term| tru]
    | leFalse {n₁ n₂: Nat} (h₁: n₁ > n₂): Eval₁ [Term| ‹nat:n₁› ≤ ‹nat:n₂›] [Term| fls]
    | gtL {t₁ t₃ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› > ‹t₃›] [Term| ‹t₂› > ‹t₃›]
    | gtR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› > ‹t₁›] [Term| ‹v₁› > ‹t₂›]
    | gtTrue {n₁ n₂: Nat} (h₁: n₁ > n₂): Eval₁ [Term| ‹nat:n₁› > ‹nat:n₂›] [Term| tru]
    | gtFalse {n₁ n₂: Nat} (h₁: n₁ ≤ n₂): Eval₁ [Term| ‹nat:n₁› > ‹nat:n₂›] [Term| fls]
    | geL {t₁ t₃ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› ≥ ‹t₃›] [Term| ‹t₂› ≥ ‹t₃›]
    | geR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› ≥ ‹t₁›] [Term| ‹v₁› ≥ ‹t₂›]
    | geTrue {n₁ n₂: Nat} (h₁: n₁ ≥ n₂): Eval₁ [Term| ‹nat:n₁› ≥ ‹nat:n₂›] [Term| tru]
    | geFalse {n₁ n₂: Nat} (h₁: n₁ < n₂): Eval₁ [Term| ‹nat:n₁› ≥ ‹nat:n₂›] [Term| fls]

    | iteTrue {t f: Term}: Eval₁ [Term| ite tru then ‹t› else ‹f›] [Term| ‹t›]
    | iteFalse {t f: Term}: Eval₁ [Term| ite fls then ‹t› else ‹f›] [Term| ‹f›]
    | ite {c₁ c₂ t f: Term} (h₁: Eval₁ c₁ c₂): Eval₁ [Term| ite ‹c₁› then ‹t› else ‹f›] [Term| ite ‹c₂› then ‹t› else ‹f›]

    | inl {t₁ t₂: Term} {ty: Ty} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| inl (‹t₁› | ‹ty›)] [Term| inl (‹t₂› | ‹ty›)]
    | inr {t₁ t₂: Term} {ty: Ty} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| inr (‹ty› | ‹t₁›)] [Term| inr (‹ty› | ‹t₂›)]
    | scaseInl {id₁ id₂: String} {t₁ t₂ t₃: Term} (h₁: Value t₁): Eval₁ [Term| case inl (‹t₁› | ‹ty›) of | inl ‹id₁› ⇒ ‹t₂› | inr ‹id₂› ⇒ ‹t₃›] ([id₁ ↦ t₁] [Term| ‹t₁›])
    | scaseInr {id₁ id₂: String} {t₁ t₂ t₃: Term} (h₁: Value t₁): Eval₁ [Term| case inr (‹ty› | ‹t₁›) of | inl ‹id₁› ⇒ ‹t₂› | inr ‹id₂› ⇒ ‹t₃›] ([id₂ ↦ t₂] [Term| ‹t₂›])
    | scase {id₁ id₂: String} {t₁ t₂ t₃ t₄: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| case ‹t₁› of | inl ‹id₁› ⇒ ‹t₃› | inr ‹id₂› ⇒ ‹t₄›] [Term| case ‹t₂› of | inl ‹id₁› ⇒ ‹t₃› | inr ‹id₂› ⇒ ‹t₄›]

    | consL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| ‹t₁› :: ‹t₃›] [Term| ‹t₂› :: ‹t₃›]
    | consR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| ‹v₁› :: ‹t₁›] [Term| ‹v₁› :: ‹t₂›]
    | lcaseNil {id₁ id₂: String} {t₁ t₂: Term}: Eval₁ [Term| case [] of | nil ⇒ ‹t₁› | ‹id₁› :: ‹id₂› ⇒ ‹t₂›] [Term| ‹t₁›]
    | lcaseCons {id₁ id₂: String} {t₁ t₂ t₃ t₄: Term} (h₁: Value t₁) (h₂: Value t₂): Eval₁ [Term| case ‹t₁› :: ‹t₂› of | nil ⇒ ‹t₃› | ‹id₁› :: ‹id₂› ⇒ ‹t₄›] ([id₁ ↦ t₁] [id₂ ↦ t₂] [Term| ‹t₄›])
    | lcase {id₁ id₂: String} {t₁ t₂ t₃ t₄: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| case ‹t₁› of | nil ⇒ ‹t₃› | ‹id₁› :: ‹id₂› ⇒ ‹t₄›] [Term| case ‹t₂› of | nil ⇒ ‹t₃› | ‹id₁› :: ‹id₂› ⇒ ‹t₄›]

    | pairL {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| (‹t₁›, ‹t₃›)] [Term| (‹t₂›, ‹t₃›)]
    | pairR {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ t₁ t₂): Eval₁ [Term| (‹v₁›, ‹t₁›)] [Term| (‹v₁›, ‹t₂›)]
    | fst {t₁ t₂: Term} (h₁: Value t₁) (h₂: Value t₂): Eval₁ [Term| fst (‹t₁›, ‹t₂›)] [Term| ‹t₁›]
    | snd {t₁ t₂: Term} (h₁: Value t₁) (h₂: Value t₂): Eval₁ [Term| snd (‹t₁›, ‹t₂›)] [Term| ‹t₂›]
    | pcaseVal {id₁ id₂: String} {t₁ t₂ t₃: Term} (h₁: Value t₁) (h₂: Value t₂): Eval₁ [Term| case (‹t₁›, ‹t₂›) of | (‹id₁›, ‹id₂›) ⇒ ‹t₃›] ([id₁ ↦ t₁] [id₂ ↦ t₂] [Term| ‹t₃›])
    | pcase {id₁ id₂: String} {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| case ‹t₁› of | (‹id₁›, ‹id₂›) ⇒ ‹t₃›] [Term| case ‹t₂› of | (‹id₁›, ‹id₂›) ⇒ ‹t₃›]

    | letL {id: String} {t₁ t₂ t₃: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| let ‹id› = ‹t₁› in ‹t₃›] [Term| let ‹id› = ‹t₂› in ‹t₃›]
    | letR {id: String} {v₁ t₁ t₂: Term} (h₁: Value v₁) (h₂: Eval₁ ([id ↦ v₁] t₁) t₂): Eval₁ [Term| let ‹id› = ‹v₁› in ‹t₁›] [Term| let ‹id› = ‹v₁› in ‹t₂›]

    | fix {t₁ t₂: Term} (h₁: Eval₁ t₁ t₂): Eval₁ [Term| fix ‹t₁›] [Term| fix ‹t₂›]
    | fixAbs {id: String} {ty: Ty} {b: Term}: Eval₁ [Term| fix (λ ‹id›: ‹ty›. ‹b›)] ([id ↦ [Term| fix (λ ‹id›: ‹ty›. ‹b›)]] [Term| ‹b›])

  scoped infix:50 "⟶" => Eval₁
  scoped infix:50 "⇓"  => SmallStep.MultiStep Eval₁

  /-
  #### Typing
  -/

  open SoftwareFoundations.LogicalFoundations.Maps

  def Context: Type := PartialMap Ty
  def Context.empty: Context := PartialMap.empty

  notation "●" => Context.empty
  notation Γ ";" id ":" ty => PartialMap.update Γ id ty

  inductive HasType: Context → Term → Ty → Prop where
    | var {Γ: Context} {id: String} {ty: Ty} (h₁: Γ id = .some ty): HasType Γ [Term| ‹id:id›] [Ty| ‹ty›]
    | abs {Γ: Context} {id: String} {ty₁ ty₂: Ty} {b: Term} (h₁: HasType (Γ; id: ty₁) b ty₂): HasType Γ [Term| λ ‹id›: ‹ty₁›. ‹b›] [Ty| ‹ty₁› → ‹ty₂›]
    | app {Γ: Context} {t₁ t₂: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ t₁ [Ty| ‹ty₁› → ‹ty₂›]) (h₂: HasType Γ t₂ [Ty| ‹ty₁›]): HasType Γ [Term| ‹t₁› ‹t₂›] [Ty| ‹ty₂›]

    | true {Γ: Context}: HasType Γ [Term| tru] [Ty| 𝔹]
    | false {Γ: Context}: HasType Γ [Term| fls] [Ty| 𝔹]
    | and {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| 𝔹]) (h₂: HasType Γ t₂ [Ty| 𝔹]): HasType Γ [Term| ‹t₁› ∧ ‹t₂›] [Ty| 𝔹]
    | or {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| 𝔹]) (h₂: HasType Γ t₂ [Ty| 𝔹]): HasType Γ [Term| ‹t₁› ∨ ‹t₂›] [Ty| 𝔹]
    | not {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t [Ty| 𝔹]): HasType Γ [Term| ¬ ‹t›] [Ty| 𝔹]
    | bcase {Γ: Context} {c t f: Term} {ty: Ty} (h₁: HasType Γ c [Ty| 𝔹]) (h₂: HasType Γ t ty) (h₃: HasType Γ f ty): HasType Γ [Term| case ‹c› of | tru ⇒ ‹t› | fls ⇒ ‹f›] [Ty| ‹ty›]

    | const {Γ: Context} {n: Nat}: HasType Γ [Term| ‹nat:n›] [Ty| ℕ]
    | succ {Γ: Context} {t: Term} (h₁: HasType Γ t [Ty| ℕ]): HasType Γ [Term| succ ‹t›] [Ty| ℕ]
    | pred {Γ: Context} {t: Term} (h₁: HasType Γ t [Ty| ℕ]): HasType Γ [Term| pred ‹t›] [Ty| ℕ]
    | add {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› + ‹t₂›] [Ty| ℕ]
    | sub {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› - ‹t₂›] [Ty| ℕ]
    | mul {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› * ‹t₂›] [Ty| ℕ]
    | div {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› / ‹t₂›] [Ty| ℕ]
    | mod {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› % ‹t₂›] [Ty| ℕ]
    | exp {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› ^ ‹t₂›] [Ty| ℕ]

    | eq {Γ: Context} {t₁ t₂: Term} {ty: Ty} (h₁: HasType Γ t₁ ty) (h₂: HasType Γ t₂ ty): HasType Γ [Term| ‹t₁› = ‹t₂›] [Ty| ‹ty›]
    | neq {Γ: Context} {t₁ t₂: Term} {ty: Ty} (h₁: HasType Γ t₁ ty) (h₂: HasType Γ t₂ ty): HasType Γ [Term| ‹t₁› ≠ ‹t₂›] [Ty| ‹ty›]
    | lt {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› < ‹t₂›] [Ty| ℕ]
    | le {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› ≤ ‹t₂›] [Ty| ℕ]
    | gt {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› > ‹t₂›] [Ty| ℕ]
    | ge {Γ: Context} {t₁ t₂: Term} (h₁: HasType Γ t₁ [Ty| ℕ]) (h₂: HasType Γ t₂ [Ty| ℕ]): HasType Γ [Term| ‹t₁› ≥ ‹t₂›] [Ty| ℕ]

    | inl {Γ: Context} {t: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ t ty₁): HasType Γ [Term| inl (‹t› | ‹ty₂›)] [Ty| ‹ty₁› + ‹ty₂›]
    | inr {Γ: Context} {t: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ t ty₂): HasType Γ [Term| inr (‹ty₁› | ‹t›)] [Ty| ‹ty₁› + ‹ty₂›]
    | scase {Γ: Context} {c l r: Term} {id₁ id₂: String} {ty₁ ty₂ ty₃: Ty} (h₁: HasType Γ c [Ty| ‹ty₁› + ‹ty₂›]) (h₁: HasType (Γ; id₁: ty₁) l ty₃) (h₂: HasType (Γ; id₂: ty₂) r ty₃): HasType Γ [Term| case ‹c› of | inl ‹id₁› ⇒ ‹t₂› | inr ‹id₂› ⇒ ‹t₃›] [Ty| ‹ty₃›]

    | nil {Γ: Context} {ty: Ty} (h₁: HasType Γ [Term| []] ty): HasType Γ [Term| []] [Ty| [‹ty›]]
    | cons {Γ: Context} {hd tl: Term} {ty: Ty} (h₁: HasType Γ hd ty) (h₂: HasType Γ tl [Ty| [‹ty›]]): HasType Γ [Term| ‹hd› :: ‹tl›] [Ty| [‹ty›]]

    | unit {Γ: Context}: HasType Γ [Term| ()] [Ty| ()]

    | pair {Γ: Context} {t₁ t₂: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ t₁ ty₁) (h₂: HasType Γ t₂ ty₂): HasType Γ [Term| (‹t₁›, ‹t₂›)] [Ty| ‹ty₁› × ‹ty₂›]
    | fst {Γ: Context} {t: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ t [Ty| ‹ty₁› × ‹ty₂›]): HasType Γ [Term| fst ‹t›] [Ty| ‹ty₁›]
    | snd {Γ: Context} {t: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ t [Ty| ‹ty₁› × ‹ty₂›]): HasType Γ [Term| snd ‹t›] [Ty| ‹ty₂›]
    | pcase {Γ: Context} {c b: Term} {id₁ id₂: String} {ty₁ ty₂ ty₃: Ty} (h₁: HasType Γ c [Ty| ‹ty₁› × ‹ty₂›]) (h₂: HasType ((Γ; id₁: ty₁); id₂: ty₂) b ty₃): HasType Γ [Term| case ‹c› of | (‹id₁›, ‹id₂›) ⇒ ‹b›] [Ty| ‹t₃›]

    | let {Γ: Context} {id: String} {t₁ t₂: Term} {ty₁ ty₂: Ty} (h₁: HasType Γ t₁ ty₁) (h₂: HasType (Γ; id: ty₁) t₂ ty₂): HasType Γ [Term| let ‹id› = ‹t₁› in ‹t₂›] [Ty| ‹ty₂›]

    | fix {Γ: Context} {t: Term} {ty: Ty} (h₁: HasType Γ t [Ty| ‹ty› → ‹ty›]): HasType Γ [Term| fix ‹t›] [Ty| ‹ty›]

  scoped notation ctx "⊢" t ":" ty => HasType ctx t ty

  /-
  ### Examples
  -/

  /-
  #### Preliminaries
  -/

  /-
  #### Numbers
  -/

  namespace NumTest
    def testTerm := [Term|
      ite (pred succ pred (2 * 0) = 0)
      then 5
      else 6
    ]

    namespace Term
      example: ● ⊢ testTerm: [Ty| ℕ] := sorry
      example: testTerm ⇓ [Term| 5] := sorry
    end Term

    namespace Tactic
    end Tactic

    namespace Blended
    end Blended
  end NumTest

  /-
  #### Products
  -/

  namespace ProdTest
    def testTerm := [Term|
      snd fst ((5, 6), 7)
    ]

    namespace Term
      example: ● ⊢ testTerm: [Ty| ℕ] := sorry
      example: testTerm ⇓ [Term| 6] := sorry
    end Term

    namespace Tactic
    end Tactic

    namespace Blended
    end Blended
  end ProdTest

  /-
  #### Let
  -/

  namespace LetTest
    def testTerm₁ := [Term|
      let x = pred 6 in
      succ x
    ]

    def testTerm₂ := [Term|
      let z = pred 6 in
      succ z
    ]

    namespace Term
      example: ● ⊢ testTerm₁: [Ty| ℕ] := sorry
      example: testTerm₁ ⇓ [Term| 6] := sorry

      example: ● ⊢ testTerm₂: [Ty| ℕ] := sorry
      example: testTerm₂ ⇓ [Term| 6] := sorry
    end Term

    namespace Tactic
    end Tactic

    namespace Blended
    end Blended
  end LetTest

  /-
  #### Sums
  -/

  namespace SumTest
    def testTerm₁ := [Term|
      case inl (5 | ℕ) of
        | inl x ⇒ x
        | inr y ⇒ r
    ]

    def testTerm₂ := [Term|
      let processSum = λ x: ℕ + ℕ.
        case x of
          | inl n ⇒ n
          | inr n ⇒ ite n = 0 then 1 else 0
      in
      (processSum (inl (5 | ℕ)), processSum (inr (ℕ | 5)))
    ]

    namespace Term
      example: ● ⊢ testTerm₁: [Ty| ℕ] := sorry
      example: testTerm₁ ⇓ [Term| 5] := sorry

      example: ● ⊢ testTerm₂: [Ty| ℕ × ℕ] := sorry
      example: testTerm₂ ⇓ [Term| (5, 0)] := sorry
    end Term

    namespace Tactic
    end Tactic

    namespace Blended
    end Blended
  end SumTest

  /-
  #### Lists
  -/

  namespace ListTest
    def testTerm := [Term|
      let l = [5, 6] in
      case l of
        | nil ⇒ 0
        | hd :: tl ⇒ hd * hd
    ]

    namespace Term
      example: ● ⊢ testTerm: [Ty| ℕ] := sorry
      example: testTerm ⇓ [Term| 25] := sorry
    end Term

    namespace Tactic
    end Tactic

    namespace Blended
    end Blended
  end ListTest

  /-
  #### Fix
  -/

  namespace FixTest
    def fact := [Term|
      fix (λ f: ℕ → ℕ. λ a: ℕ.
        ite (a = 0)
        then 1
        else a * (f (pred a))
      )
    ]

    def map := [Term|
      λ g: ℕ → ℕ.
        fix (λ f: [ℕ] → [ℕ]. λ l: [ℕ].
          case l of
            | nil ⇒ []
            | hd :: tl ⇒ g hd :: f tl)
    ]

    def equal := [Term|
      fix (λ eq: ℕ → ℕ → 𝔹. λ m: ℕ. λ n: ℕ.
        ite m = 0
        then ite n = 0
             then tru
             else fls
        else ite n = 0
             then fls
             else eq (pred m) (pred n))
    ]

    def evenOdd := [Term|
      let evenOdd = fix (λ evenOdd: ((ℕ → ℕ) × (ℕ → ℕ)).
        ((λ n: ℕ. ite n = 0 then tru else (snd evenOdd) (pred n)),
         (λ n: ℕ. ite n = 0 then fls else (fst evenOdd) (pred n)))
      ) in
      let even = fst evenOdd in
      let odd = snd evenOdd in
      (even 3, even 4)
    ]

    namespace Term
      example: ● ⊢ fact: [Ty| ℕ → ℕ] := sorry
      example: [Term| ‹fact› 4] ⇓ [Term| 24] := sorry

      example: ● ⊢ map: [Ty| (ℕ → ℕ) → ([ℕ] → [ℕ])] := sorry
      example: [Term| ‹map› (λ x: ℕ. succ x) [1, 2]] ⇓ [Term| 24] := sorry

      example: ● ⊢ equal: [Ty| ℕ → ℕ → 𝔹] := sorry
      example: [Term| ‹equal› 4 4] ⇓ [Term| tru] := sorry
      example: [Term| ‹equal› 4 5] ⇓ [Term| fls] := sorry

      example: ● ⊢ evenOdd: [Ty| 𝔹 × 𝔹] := sorry
      example: evenOdd ⇓ [Term| (fls, tru)] := sorry
    end Term

    namespace Tactic
    end Tactic

    namespace Blended
    end Blended
  end FixTest

  /-
  ### Properties of Typing
  -/

  /-
  #### Progress
  -/

  namespace Term
    theorem HasType.progress {t₁: Term} {ty: Ty}: (● ⊢ t₁ : ty) → Value t ∨ ∃ t₂: Term, t₁ ⟶ t₂ := sorry
  end Term

  namespace Tactic
  end Tactic

  namespace Blended
  end Blended

  /-
  #### Weakening
  -/

  namespace Term
    theorem Context.weakening {Γ₁ Γ₂: Context} {t: Term} {ty: Ty}: Γ₁.includedIn Γ₂ → (Γ₁ ⊢ t : ty) → Γ₂ ⊢ t : ty := sorry
    theorem Context.weakening.empty {Γ: Context} {t: Term} {ty: Ty}: (● ⊢ t : ty) → Γ ⊢ t : ty := sorry
  end Term

  namespace Tactic
  end Tactic

  namespace Blended
  end Blended

  /-
  #### Substitution
  -/

  namespace Term
    theorem Term.subst.preservation {Γ: Context} {id: String} {t₁ t₂: Term} {ty₁ ty₂: Ty}: (Γ.update id ty₁ ⊢ t₁ : ty₂) → (● ⊢ t₂ : ty₁) → Γ ⊢ (Term.subst id t₂ t₁) : ty₂ := sorry
  end Term

  namespace Tactic
  end Tactic

  namespace Blended
  end Blended

  /-
  #### Preservation
  -/

  namespace Term
    theorem HasType.preservation {t₁ t₂: Term} {ty: Ty}: (● ⊢ t₁ : ty) → (t₁ ⟶ t₂) → (● ⊢ t₂ : ty) := sorry
  end Term

  namespace Tactic
  end Tactic

  namespace Blended
  end Blended
end SoftwareFoundations.ProgrammingLanguageFoundations.MoreStlc
