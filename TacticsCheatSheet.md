Coq <-> Lean4 Tactics Cheat Sheet
===

This is a list of Coq tactics and their (rough) equivalent in Lean4.  It's
important to note that these are often not *quite* equivalent.

Tactics
---

| Coq | Lean | Notes |
| - | - | - |
| `intros` | `intro` | Lean4 also supports pattern matching |
| `reflexivity` | `rfl` | |
| `apply` | `apply` | |
| `apply ... in` | ??? | How do I do an `apply` to a hypothesis in the context? |
| `apply ... with` | `apply` | Supports explicit positional args (`apply foo 1 2 3`) or named args (`apply foo (x := 1) (z := 3)`) |
| `simpl` | `simp` | Also has variants `simp [... theorems ...]`, `simp only [... theorems ...]`, `simp_all`, and other more specialized varieties.  Theorems can be added to the simplifier using the `@[simp]`, `@[local simp]` (restricted to the current file), and `@[scoped simp]` (restricted to the current scope and all sub-scopes) annotations.  Any theorem added to the simplifier should "make progress" when read left to right.  So `x + 0 = x` is a good candidate, but `x + y = y + x` is not. |
| `simpl in h` | `simp at h` | |
| `rewrite` | `rw` (or `rewrite`) | Automatically calls `try rfl` |
| `rewrite ... in h` | `rw ... at h` | |
| `symmetry` | `symm` | Requires `import Mathlib.Tactic.Relation.Symm` and only works on Symmetric relations |
| `symmetry at h` | `symm at h` | Same notes as `symm` |
| `transitivity` | `trans` | Requires `import Mathlib.Tactic.Relation.Trans` and only works on Transitive relations, also supports `trans at h` |
| `unfold` | `unfold` (related: `@[reducible]`/`abbrev`) | The `@[reducible]` annotation on a definition allows tactics to auto-unfold the a definition (`@[reducible] def foo := ...`).  The `abbrev` is an abbreviation (typically for a type) which is reducible (`abbrev Sum: Type := List Parts`).  See [this StackExchange post](https://proofassistants.stackexchange.com/questions/2457/what-is-the-precise-meaning-of-reducible) for more details. |
| `unfold ... in h` | `unfold ... at h` | |
| `destruct ... as`, `destruct ... eqn` | `cases ...` | |
| `induction ... as ...` | `induction ... with` | |
| `injection` | ??? | ??? |
| `discriminate` | ??? | ??? |
| `assert (H: e)` or `assert (e) as H` | `have h: ... := ...` | `have` is very similar to a local `let` binding.  The name is optional, and defaults to the name `this`. |
| `generalize dependent` | `generalize` or `revert` | ???.  Not sure which... |
| `f_equal` | `funext` | ???.  Maybe? |
| | `contradiction` | Handles a lot of cases, some of which are covered by the Coq `injection` and `discriminate` tactics (I think...). |
| `left`, `right` | ??? | |
| `inversion` | ??? | Really want to figure this one out |
| `lia` | `linarith` | Requires `import Mathlib.tactic.linarith` |
| `clear` | `clear` | |
| `rename ... into ...` | `rename ... => ...` | |
| `assumption` | `assumption` | |
| `constructor` | `constructor` | |
| `auto` | ??? | |
| `eapply` | `eapply` | |
| `congruence` | `congr` | |
| `intuition` | ??? | |

Tacticals
---

| Coq | Lean | Notes |
| `try` | `try` | |
| `;` | `<;>` | |
| `repeat` | `repeat` | |
| `subst` | `subst` | |

Other
---

Some Coq tactics allow referencing the goal as `goal`.  Lean doesn't seem to
have the same functionality.