def andThen (opt: Option α) (next: α → Option β): Option β :=
  match opt with
    | none => none
    | some x => next x

infixl:55 " ~~> " => andThen

def first (lst: List α): Option α :=
  lst[0]?

def firstThird (lst: List α): Option (α × α) :=
  lst[0]? ~~> fun fst =>
  lst[2]? ~~> fun third =>
  some (fst, third)

def firstThirdFifth (lst: List α): Option (α × α × α) :=
  lst[0]? ~~> fun fst =>
  lst[2]? ~~> fun third =>
  lst[4]? ~~> fun fifth =>
  some (fst, third, fifth)

def firstThirdFifthSeventh (lst: List α): Option (α × α × α × α) :=
  lst[0]? ~~> fun fst =>
  lst[2]? ~~> fun third =>
  lst[4]? ~~> fun fifth =>
  lst[6]? ~~> fun seventh =>
  some (fst, third, fifth, seventh)





def ok (x: α): Except ε α := Except.ok x
def fail (e: ε): Except ε α := Except.error e

def get (lst: List α) (n: Nat): Except String α :=
  match lst[n]? with
    | none => fail s!"Index {n} not found in list of length {lst.length}"
    | some x => ok x

def ediblePlants: List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]

#eval get ediblePlants 2
#eval get ediblePlants 43

def andThen' (attempt: Except ε α) (next: α → Except ε β): Except ε β :=
  match attempt with
    | Except.error e => fail e
    | Except.ok res => next res

infixl:55 " ~~~>> " => andThen'

def first' (lst: List α): Except String α :=
  get lst 0

def firstThird' (lst: List α): Except String (α × α) :=
  get lst 0 ~~~>> fun first =>
  get lst 2 ~~~>> fun third =>
  ok (first, third)

def firstThirdFifth' (lst: List α): Except String (α × α × α) :=
  get lst 0 ~~~>> fun first =>
  get lst 2 ~~~>> fun third =>
  get lst 4 ~~~>> fun fifth =>
  ok (first, third, fifth)

def firstThirdFifthSeventh' (lst: List α): Except String (α × α × α × α) :=
  get lst 0 ~~~>> fun first =>
  get lst 2 ~~~>> fun third =>
  get lst 4 ~~~>> fun fifth =>
  get lst 6 ~~~>> fun seventh =>
  ok (first, third, fifth, seventh)


structure WithLog (logged: Type) (α: Type) where
  log: List logged
  val: α
deriving Repr

def andThen'' (result: WithLog α β) (next: β → WithLog α γ): WithLog α γ :=
  let ⟨out, res⟩ := result
  let ⟨out', res'⟩ := next res
  ⟨out ++ out', res'⟩

infixr:55 " ~~~~>>> " => andThen''

def unlogged (x: β): WithLog α β := ⟨[], x⟩
def save (data: α): WithLog α Unit := ⟨[data], ()⟩

def isEven (i: Int): Bool :=
  i % 2 == 0

def sumAndFindEvens: List Int → WithLog Int Int
  | [] => unlogged 0
  | hd :: tl =>
    (if isEven hd then save hd else unlogged ()) ~~~~>>> fun () =>
    sumAndFindEvens tl ~~~~>>> fun sum =>
    unlogged sum

inductive BinTree (α: Type) :=
  | leaf: BinTree α
  | node: BinTree α → α → BinTree α → BinTree α

def inOrderSum: BinTree Int → WithLog Int Int
  | BinTree.leaf => unlogged 0
  | BinTree.node tₗ x tᵣ =>
    inOrderSum tₗ ~~~~>>> fun sₗ =>
    inOrderSum tᵣ ~~~~>>> fun sᵣ =>
    unlogged (sₗ + x + sᵣ)



def State (σ: Type) (α: Type): Type :=
  σ → (σ × α)

def same (x: α): State σ α :=
  fun s => (s, x)

def read: State σ σ :=
  fun s => (s, s)

def update (s: σ): State σ Unit :=
  fun _ => (s, ())

def andThen''' (first: State σ α) (next: α → State σ β): State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~~~~>>>> " => andThen'''

def aTree :=
  BinTree.node
    (BinTree.node
       (BinTree.node BinTree.leaf "a" (BinTree.node BinTree.leaf "b" BinTree.leaf))
       "c"
       BinTree.leaf)
    "d"
    (BinTree.node BinTree.leaf "e" BinTree.leaf)

def number (t: BinTree α): BinTree (Nat × α) :=
  let rec helper: BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => same BinTree.leaf
    | BinTree.node tₗ x tᵣ =>
      helper tₗ ~~~~~>>>> fun tₗₙ =>
      read ~~~~~>>>> fun nₗ =>
      update (nₗ + 1) ~~~~~>>>> fun () =>
      helper tᵣ ~~~~~>>>> fun tᵣₙ =>
      same (BinTree.node tₗₙ (nₗ, x) tᵣₙ)
  (helper t 0).snd

instance: Monad Option where
  pure x := some x
  bind x f :=
    match x with
      | none => none
      | some x => f x

instance: Monad (Except ε) where
  pure x := Except.ok x
  bind x f :=
    match x with
      | Except.error e => Except.error e
      | Except.ok x => f x

def firstThirdFifthSeventhMonad [Monad m] (lookup: List α → Nat → m α) (lst: List α): m (α × α × α × α) :=
  lookup lst 0 >>= fun first =>
  lookup lst 2 >>= fun third =>
  lookup lst 4 >>= fun fifth =>
  lookup lst 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventhMonad (fun lst i => lst[i]?) slowMammals
#eval firstThirdFifthSeventhMonad (fun lst i => lst[i]?) fastBirds

def getOrExcept (lst: List α) (n: Nat): Except String α :=
  match lst[n]? with
    | none => Except.error s!"Index {n} not found in list of size {lst.length}"
    | some x => Except.ok x

#eval firstThirdFifthSeventhMonad getOrExcept slowMammals
#eval firstThirdFifthSeventhMonad getOrExcept fastBirds

def mapM [Monad m] (f: α → m β): List α → m (List β)
  | [] => pure []
  | hd :: tl =>
    f hd >>= fun hd =>
    mapM f tl >>= fun tl =>
    pure (hd :: tl)

instance: Monad (State σ) where
  pure x := fun s => (s, x)
  bind x f :=
    fun s =>
      let (s', x) := x s
      f x s'

def increment (amt: Int): State Int Int :=
  read >>= fun v =>
  update (v + amt) >>= fun () =>
  pure v

#eval mapM increment [1, 2, 3, 4, 5] 0

instance: Monad (WithLog logged) where
  pure x := ⟨[], x⟩
  bind x f :=
    let ⟨out, res⟩ := x
    let ⟨out', res⟩ := f res
    ⟨out ++ out', res⟩

def saveIfEven (i: Int): WithLog Int Int :=
  (if isEven i then save i else pure ()) >>= fun () =>
  pure i

#eval mapM saveIfEven [1, 2, 3, 4, 5]

instance: Monad Id where
  pure x := x
  bind x f := f x

#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]
