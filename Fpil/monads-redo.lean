/-
# 5. Monads
-/

/- Options -/

def Option.andThen (o: Option α) (next: α → Option β): Option β :=
  match o with
    | .none => .none
    | .some v => next v

infixl:55 ">o>" => Option.andThen

def Option.first (l: List α): Option α :=
  l[0]?

def Option.firstThird (l: List α): Option (α × α) :=
  Option.first l >o> fun first =>
  l[2]? >o> fun third =>
  some (first, third)

def Option.firstThirdFifth (l: List α): Option (α × α × α) :=
  firstThird l >o> fun (first, third) =>
  l[4]? >o> fun fifth =>
  some (first, third, fifth)

def Option.firstThirdFifthSeventh (l: List α): Option (α × α × α × α) :=
  firstThirdFifth l >o> fun (first, third, fifth) =>
  l[6]? >o> fun seventh =>
  some (first, third, fifth, seventh)

/- Errors -/

def List.getExcept (l: List α) (n: Nat): Except String α :=
  match l[n]? with
    | .none => Except.error s!"Index {n} not found in list of size {l.length}"
    | .some v => Except.ok v

def Except.andThen (e: Except ε α) (next: α → Except ε β): Except ε β :=
  match e with
    | .error e => .error e
    | .ok v => next v

infixl:55 ">!>" => Except.andThen

def Except.first (l: List α): Except String α :=
  l.getExcept 0

def Except.firstThird (l: List α): Except String (α × α) :=
  Except.first l >!> fun first =>
  l.getExcept 2 >!> fun third =>
  Except.ok (first, third)

def Except.firstThirdFifth (l: List α): Except String (α × α × α) :=
  Except.firstThird l >!> fun (first, third) =>
  l.getExcept 4 >!> fun fifth =>
  Except.ok (first, third, fifth)

def Except.firstThirdFifthSeventh (l: List α): Except String (α × α × α × α) :=
  Except.firstThirdFifth l >!> fun (first, third, fifth) =>
  l.getExcept 6 >!> fun seventh =>
  Except.ok (first, third, fifth, seventh)

/- Logging -/

inductive BinTree (α: Type): Type where
  | leaf: BinTree α
  | branch: BinTree α → α → BinTree α → BinTree α
deriving BEq, Hashable, Repr

def Int.isEven (i: Int): Bool := i % 2 == 0

structure WithLog (α β: Type) where
  log: List α
  val: β

def WithLog.andThen (input: WithLog α β) (next: β -> WithLog α γ): WithLog α γ :=
  let output := next input.val
  ⟨input.log ++ output.log, output.val⟩

infixr:55 ">l>" => WithLog.andThen

def WithLog.ok (val: β): WithLog α β :=
  ⟨[], val⟩

def WithLog.save (data: α): WithLog α Unit :=
  ⟨[data], ()⟩

def WithLog.sumAndFindEvens: List Int → WithLog Int Int
  | [] => WithLog.ok 0
  | hd :: tl =>
    (if hd.isEven
     then WithLog.save hd
     else WithLog.ok ()) >l> fun () =>
    sumAndFindEvens tl >l> fun sum =>
    WithLog.ok (hd + sum)

def WithLog.inorderSum: BinTree Int → WithLog Int Int
  | .leaf => WithLog.ok 0
  | .branch tₗ x tᵣ =>
    inorderSum tₗ >l> fun sumₗ =>
    WithLog.save x >l> fun () =>
    inorderSum tᵣ >l> fun sumᵣ =>
    WithLog.ok (sumₗ + x + sumᵣ)

/- State -/

def State (σ α: Type): Type := σ → (σ × α)

def State.andThen (state: State σ α) (next: α -> State σ β): State σ β :=
  fun s =>
    let (s', x) := state s
    next x s'

infixr:55 ">#>" => State.andThen

def State.ok (x: α): State σ α :=
  fun s => (s, x)

def State.get: State σ σ :=
  fun s => (s, s)

def State.set (x: σ): State σ Unit :=
  fun _ => (x, ())

def BinTree.number (t: BinTree α): BinTree (Nat × α) :=
  let rec number (t: BinTree α): State Nat (BinTree (Nat × α)) :=
    match t with
      | .leaf => State.ok .leaf
      | .branch tₗ x tᵣ =>
        number tₗ >#> fun tₗ =>
        State.get >#> fun n =>
        State.set (n + 1) >#> fun () =>
        number tᵣ >#> fun tᵣ =>
        State.ok (.branch tₗ (n, x) tᵣ)
  (number t 0).snd

/-
# 5.1 The Monad Type Class
-/

/- Generic -/

/- TODO: Revisit -/
def mapM [Monad m] (f: α -> m β): List α → m (List β)
  | [] => pure []
  | hd :: tl =>
    f hd >>= fun hd =>
    mapM f tl >>= fun tl =>
    pure (hd :: tl)

/- Options and Error -/

instance: Monad Option where
  pure := .some
  bind x f :=
    match x with
      | .none => none
      | .some x => f x

instance: Monad (Except ε) where
  pure x := Except.ok x
  bind x f :=
    match x with
      | .error e => .error e
      | .ok x => f x

def first [Monad m] (lookup: List α → Nat → m α) (l: List α): m α :=
  lookup l 0

def firstThird [Monad m] (lookup: List α → Nat → m α) (l: List α): m (α × α) :=
  lookup l 0 >>= fun first =>
  lookup l 2 >>= fun third =>
  pure (first, third)

def firstThirdFifth [Monad m] (lookup: List α → Nat → m α) (l: List α): m (α × α × α) :=
  lookup l 0 >>= fun first =>
  lookup l 2 >>= fun third =>
  lookup l 4 >>= fun fifth =>
  pure (first, third, fifth)

def firstThirdFifthSeventh [Monad m] (lookup: List α → Nat → m α) (l: List α): m (α × α × α × α) :=
  lookup l 0 >>= fun first =>
  lookup l 2 >>= fun third =>
  lookup l 4 >>= fun fifth =>
  lookup l 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

/- Errors -/

def firstExcept (l: List α): Except String α :=
  l.getExcept 0

def firstThirdExcept (l: List α): Except String (α × α) :=
  firstExcept l >>= fun first =>
  l.getExcept 2 >>= fun third =>
  pure (first, third)

def firstThirdFifthExcept (l: List α): Except String (α × α × α) :=
  firstThirdExcept l >>= fun (first, third) =>
  l.getExcept 4 >>= fun fifth =>
  pure (first, third, fifth)

def firstThirdFifthSeventhExcept (l: List α): Except String (α × α × α × α) :=
  firstThirdFifthExcept l >>= fun (first, third, fifth) =>
  l.getExcept 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

/- Logging -/

instance: Monad (WithLog α) where
  pure x := ⟨[], x⟩
  bind x f :=
    let ⟨log, res⟩ := f x.val
    ⟨x.log ++ log, res⟩

def sumAndFindEvens: List Int → WithLog Int Int
  | [] => pure 0
  | hd :: tl =>
    (if hd.isEven
     then WithLog.save hd
     else pure ()) >>= fun () =>
    sumAndFindEvens tl >>= fun sum =>
    pure (hd + sum)

def inorderSum: BinTree Int → WithLog Int Int
  | .leaf => pure 0
  | .branch tₗ x tᵣ =>
    inorderSum tₗ >>= fun sumₗ =>
    WithLog.save x >>= fun () =>
    inorderSum tᵣ >>= fun sumᵣ =>
    pure (sumₗ + x + sumᵣ)

/- TODO: Revisit -/
def saveIfEven (i: Int): WithLog Int Int :=
  (if i.isEven then WithLog.save i else pure ()) >>= fun () =>
  pure i

/- State -/

instance: Monad (State σ) where
  pure x := fun s => (s, x)
  bind x f :=
    fun s =>
      let (s', x) := x s
      f x s'

def number (t: BinTree α): BinTree (Nat × α) :=
  let rec number (t: BinTree α): State Nat (BinTree (Nat × α)) :=
    match t with
      | .leaf => pure .leaf
      | .branch tₗ x tᵣ =>
        number tₗ >>= fun tₗ =>
        State.get >>= fun n =>
        State.set (n + 1) >>= fun () =>
        number tᵣ >>= fun tᵣ =>
        pure (.branch tₗ (n, x) tᵣ)
  (number t 0).snd

/- TODO: Revisit -/
def increment (amt: Int): State Int Int :=
  State.get >>= fun curr =>
  State.set (curr + amt) >>= fun () =>
  pure curr

/- Identity -/

instance: Monad Id where
  pure x := x
  bind x f := f x

/- Exercises -/

def BinTree.mapM [Monad m] (f: α → m β): BinTree α → m (BinTree β)
  | .leaf => pure .leaf
  | .branch tₗ x tᵣ =>
    f x >>= fun x =>
    mapM f tₗ >>= fun tₗ =>
    mapM f tᵣ >>= fun tᵣ =>
    pure (.branch tₗ x tᵣ)

/-
# 5.2 Example: Arithmetic in Monads
-/

inductive Expr (op: Type): Type where
  | const: Int → Expr op
  | prim: op → Expr op → Expr op → Expr op

inductive Arith: Type where
  | plus
  | minus
  | times
  | div

def twoPlusThree: Expr Arith :=
  Expr.prim Arith.plus (Expr.const 2) (Expr.const 3)
