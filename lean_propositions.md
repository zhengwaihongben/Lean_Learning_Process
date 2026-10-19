# Propositions

This chapter introduces the type of propositions `Prop` in Lean, and we will see the core philosophy of Dependent Types Theory and Lean: "Propositions as types, proofs as terms".

In Lean 4, the propositions are also a type:
```lean
#check 1 + 1 = 2
-- 1 + 1 = 2 : Prop
#check Prop
-- Prop : Type
```
"Propositions as types, proofs as terms" means that when we declare a proposition, we are essentially declare a new type, and the proof is the construction of a term of the type. This perspective is central to constructive logic, where truth means having an explicit proof.

We will keep see that later.

## `theorem` command and some proofs

`theorem` command is essentially a specific version of `def` to the proofs. Syntax:
```lean
theorem name (parameter : type) : statement := by
  proof
```
Basically, we define a new type `statement`, and `name` is an abstract term of the new type. The process of `proof` is to construct an explicit term of the type. `by` is to enter the tactic mode. This can be seen by
```lean
#check name
-- name : statement
```

For example:
```lean
variable (P Q R : Prop)
theorem syllogism (h : P → Q)(q : Q → R) : P → R := by
  intro h1
  apply q
  apply h
  exact h1
#check syllogism
-- syllogism (P Q R : Prop) (h : P → Q) (q : Q → R) : P → R
```
`syllogism` is an object of type `P → R`.

For readability, Lean 4 also provides `lemma` commad, which has the same functions to `theorem`.

### `apply` tactic

`apply` is to substitute the current goal into an established result, which can be understood as applying an established result. In the previous example, when the cursor is on
1. `intro h1`: our goal is `R` and now we let `h1` be `p`

    ```Lean InfoView
    P Q R : Prop
    h : P → Q
    q : Q → R
    h1 : P
    ⊢ R
    ```

2. `apply q`: since `Q → R`, we just need to prove(construct) `Q`

    ```Lean InfoView
    P Q R : Prop
    h : P → Q
    q : Q → R
    h1 : P
    ⊢ Q
    ```

3. `apply p`: similar to 2. We just need to construct `P`

    ```Lean InfoView
    P Q R : Prop
    h : P → Q
    q : Q → R
    h1 : P
    ⊢ P
    ```

4. `exact h1`: we already have `P` in `h1` so we just provide `P` and finish the proof.

### `have` command

`have` command is to introduce an intermediate result(lemma in math) and its proof within a proof. Syntax:
```lean
theorem name : statement := by
  have name2 : statement2 :=
    proof2
  proof1
```
It is similar to `let` which is define a local constant or varibale.

### `... ?`

This is a powerful function of Lean 4 called automated search.

In a proof, when you have a few established results, you can type `apply?` and then Lean finds the appropriate result automatically. InfoView then returns a prompt
```Lean InfoView
Try this: [apply] ...
```
if the correct result does exist, and you can click `[apply]`. `apply?` finds the results that can derive the goal. 

There are some other similar commands:
- `exact?`: find the terms that is of the same type to the goal.
- `rw?`
- `simp?`

For example:
```lean
variable (P Q R : Prop)
theorem syllogism (h : P → Q)(q : Q → R) : P → R := by
  intro h1
  apply q
  apply?
  /-
  Try this:
    [apply] exact (h ∘ fun a => h1) P
  -/
```

### `example` command

`example` is to define an anonymous theorem without giving a name and the result is not callable. Syntax:
```lean
example (parameter : type) : statement := by
  proof
```

### `sorry` command

`sorry` in Lean is to temporarily skip the proof of a theorem or definition. It is like "let's accept this result first". Syntax:
```lean
theorem name : statement := by
  sorry
-- name is accepted although we have not give a proof yet.
```

### Calling established Theorems

Once a theorem is proven, we can call it within aother proofs.

Suppose `the1` with parameters `p1` is proven, and we now need to prove `the2`:
1. Directly applying:

    ```lean
    theorem the 2 ... := by
        the1 p1
    ```

2. By `exact`: when the conclusion of `the1` is exactly of the type of the goal

    ```lean
    exact the1 p1
    ```

3. By `apply`: to disassemble the goal

    ```lean
    apply the1
    ```

For example:
```lean
theorem my_thm (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := by
  apply h1
  exact h2

example (A B : Prop) (hAB : A → B) (hA : A) : B := by
  exact my_thm A B hAB hA
```


## Logical Connectives

### Conjunction

The logical `And` connective, represented by `∧`(`\and`) is used to objectin the conjunction of two propositions. `P ∧ Q` is true whenever both `P` and `Q` are true, and is false otherwise. We can both type a conjunction by `P ∧ Q` and `And P Q`.

The essence of `∧` is also a constructor:
```lean
#print And
/-
structure And (a b : Prop) : Prop
number of parameters: 2
fields:
  And.left : a
  And.right : b
constructor:
  And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
-/
```
For `P ∧ Q`, we have to provide the proof of both `P` and `Q`. 

To disassemble a conjunction, we usually use `exact`. Suppose We have `h : P ∧ Q`, we can use `exact h.left` to take `h`, and so `exact h.right`. For example:
```lean
example (p : P ∧ Q): P := by
  exact And.left p
```

We can also use `And.intro p q` to construct `p ∧ q` in a proof. For example:
```lean
example (p : P)(q : Q) : P ∧ Q := by
  exact And.intro p q
```

### Disjunction

The logical `Or` connective, represented by the symbol `∨`(`\or`), is used to obtain the disjunction of two propositions. `P ∨ Q` is false whenever both `P` and `Q` are false, and is true otherwise. We can both type a disjunction by `P ∨ Q` and `Or P Q`.

Similar to the conjunction, `∨` is also a constructor, but it is an inductive constructor:
```lean
#print Or
/-
inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
```

Within a proof, we can construct a disjunction by `Or.inl h` which injects `h` into the left of current goal and forms `h ∨ Goal`, and `Or.inr h` which similarly forms `Goal ∨ h`.
```lean
theorem ThOrInl (h : P) : P ∨ Q := by
  exact Or.inl h
```

Unlike the conjunction which has `And.left` and `And.right`, we must use `case` or `match` to disassemble a disjunction, or `Or.elim` which receives `P ∨ Q` and requires the proofs of `P` and `Q` in order.
```lean
theorem ThOrCases3 (h : P ∨ Q) : Q ∨ P := by
  apply Or.elim h
  -- Case P
  intro hP
  exact Or.inr hP
  -- Case Q
  intro hQ
  exact Or.inl hQ
```
when the cursor is on `apply Or.elim h`, InfoView returns:
```InfoView
2 goals
case left
P Q : Prop
h : P ∨ Q
⊢ P → Q ∨ P
case right
P Q : Prop
h : P ∨ Q
⊢ Q → Q ∨ P
```

### Implication

The logical implication connective, represented by the symbol `→` (`\to`), is used to combine two propositions and describe a conditional relationship between them. `P → Q` is false whenever `P` is true and `Q` is false, and is true otherwise.

In Lean 4, `P → Q` is actually a function type that receives a term of `P` and then returns a term of `Q`. 
```lean
theorem ThImpIn (hQ : Q) : P → Q := by
  intro hP
  exact hQ
```
We use `intro` to introduce `P`, and we do not need to gurantee the validity of `P` because of the nature of implication(Vacuous Truth).
```lean
theorem ThModusPonens (h : P → Q) (hP : P) : Q := by
  exact h hP
```
```lean
theorem ThModusPonens2 (h : P → Q) (hP : P) : Q := by
  apply h
  -- goal turns from Q to P
  exact hP
```

And compared to the types of forms `Nat → Nat`, they differ from the objects mapped. `P → Q` is a map between propositions.

### Double Implication

Double implication is also known as "if and only if"(iff), represented by `↔`(`\iff`), and it is used to combine two propositions, expressing a biconditional relationship between them.

We can type an iff by both `P ↔ Q` and `Iff P Q`.
```lean
#print Iff
/-
structure Iff (a b : Prop) : Prop
number of parameters: 2
fields:
  Iff.mp : a → b
  Iff.mpr : b → a
constructor:
  Iff.intro {a b : Prop} (mp : a → b) (mpr : b → a) : a ↔ b
-/
```
The constructor of `Iff` is `Iff.intro` which receive `a → b` and `b → a`, and then return the proposition `a ↔ b`. `Iff.mp` refers to `a → b` and `Iff.mpr` refers to `b → a`. For example:
```lean
theorem ThIffin (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  exact Iff.intro h1 h2
```
We can use `apply Iff.intro` to disassemble `P ↔ Q`:
```lean
theorem ThIffin2 (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  apply Iff.intro：
  -- 1. ⊢ P → Q
  -- 2. ⊢ Q → P
  exact h1
  exact h2
```
which is similar to `apply And.intro`. And, we can use `Iff.mp` and `Iff.mpr` to extract the two direction of an iff:
```lean
example (h: P ↔ Q) : P → Q := by
  exact Iff.mp h
```

### True and False

`True` and `False` are two logical constants. Their types are also `Prop`:
```lean
#check True
-- True : Prop
#check False
-- False : Prop
```
And, both of `True` and `False` are inductive type:
```lean
#print True
/-
inductive True : Prop
number of parameters: 0
constructors:
True.intro : True
-/
#print False
/-
inductive False : Prop
number of parameters: 0
constructors:
-/
```
`True` has only one constructor `True.intro` which can be used to prove `True`.
```lean
theorem my_true : True := by
  /-
  1 goal
  ⊢ True
  -/
  exact True.intro
```
And, `False` is also an inductive type but without any constructor. This means that no terms or proofs of type False can exist. The existence of `False` is legal, its definition is exactly the type without any elements.(We will introduce the concept of empty in Lean afterward)

`False.elim` is to construct a proof of `False → C` where `C` is a given type.
```lean
#print False.elim
-- False.elim : {C : Sort u} → False → C
```
```lean
theorem ThExFalso : False → P := by
  intro h
  exact False.elim h
```

### Negation

The logical Not connective, represented by the symbol `¬`(`\not`), is to obtain the negation of a proposition. It can be typed by both `Not P` and `¬P`. 
```lean
#print Not
/-
def Not : Prop → Prop :=
fun a => a → False
-/
```
that means `¬` is essentially a function `a → False`, thus to prove `¬P`, we need to show that assuming `P` leads to a contradiction.

To prove `¬P`, we need to construct a `False`. For example:
```lean
theorem ThModusTollens (h1 : P → Q) (h2 : ¬Q) : ¬P := by
  -- ⊢ ¬P
  intro h3  -- ⊢ False , because ¬ is P → False
  have h4 : Q :=by  -- introduce h4 : Q so that ⊢ Q
    exact h1 h3  -- we have h1 : P → Q and h3 : P, so we can use h1 and h3 to get Q
  exact h2 h4  -- ⊢ False , we now have Q and by h2, we get False.
```

We conclude that:

| Logics | Notation | Type | Constructors / Prove | Way to extract |
| :--- | :--- | :--- | :--- | :--- |
| **And** | `P ∧ Q` | structural | `And.intro` | `h.left`, `h.right` |
| **Or** | `P ∨ Q` | inductive | `Or.inl hP`, `Or.inr hQ` | `cases h` |
| **Implication** | `P → Q` | functional | `intro hP` | `h hP` or `apply h` |
| **Iff** | `P ↔ Q` | structural | `Iff.intro h1 h2` | `h.mp`, `h.mpr` |
| **True** | `True` | inductive | `True.intro` / `trivial` | unable to be extracted |
| **False** | `False` | inductive | unable to be constructed | `False.elim h` / `cases h` |
| **Negation** | `¬P` | functional | `intro hP`and then `False` | `h hP` and then `False` |

