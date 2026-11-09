# Natural Numbers

Recall that the natrual numbers $\N$ in mathematics is defined by Peano's Axioms. In Lean 4, `Nat` type is an inductive type, which has the same idea to Peano's Axioms. We can also reason by case analysis and mathematical induction once `Nat` is defined, and we can define functions on natural numbers using recursion.

## Definition

By `#print Nat`, we see how `Nat` is constructed in Lean:
```lean
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
```
which shows that `Nat` is an inductive type with two constructors: `Nat.zero` and `Nat.succ`. We will discuss the detail about this two constructors later.

Inductive types not only specify how values are built, but also provide fundamental principles of recursion and induction. These principles allow functions to be defined by pattern matching on constructors and proofs to be carried out using structural induction.

We can define a new inductive type by keyword `inductive` in Lean 4, which defines a type by finite cases and the combination of these cases.
```lean
inductive N : Type where
  | Z : N 
  | S : N → N 
deriving Repr
```
This code define a new type `N`, which is essentially equivalent(isomorphic) to `Nat`.
- `inductive`: keyword to define an inductive type
- `where`: keyword to clarify the constructor of the type
- `| Z : N`: a constructor called `Z`, which is of type `N`
- `| S : N → N`: a constructor called `S`, which is a fucntion `N → N`. That means if `n` is of type `N`, then `S n` is also of type `N`.
- `deriving Repr`: 

    It is a syntax candy used to automatically generate an instance of the `Repr` type class for a user-defined type. `Repr` class defines how values of a type can be converted into a human-readable format.

Without `deriving Repr`, Lean does not know how to print the terms of `N`, so that if we want to print a term, some errors may be returned. And to do so, we have to tell Lean by hands:
```lean
instance : Repr N where
  reprPrec n prec :=
    match n with
    | N.Z => Std.Format.text "N.Z"
    | N.S m => Std.Format.text "N.S (" ++ reprPrec m (prec + 1) ++ Std.Format.text ")"
```
Thus, `deriving Repr` is to automize this process.

Now, we successfully define `N`
```lean
inductive N : Type
number of parameters: 0
constructors:
N.Z : N
N.S : N → N
```
A specify term of `N` is `Z`:
```lean
#check N.Z
-- N.Z : N
```
and we can express the other terms in `N` inductively:
```lean
#check N.S N.Z    -- N.Z.S : N
#check N.S (N.S N.Z)    -- N.Z.S.S : N
```
If you do not want to write the prefix, use `open N`.

Here, `N.Z` is actually corresponded to `0 : Nat`, and `N.S` is the successor function.

## Cases and Match

If `x` is a variable of an inductive type in the goal, we can use `cases x` to splits the goal into the cases of the constructors. For instance, we can define a function `N → Bool` such that `true` is returned when `n` is `N.Z`, and `false` otherwise:
```lean
def Eqzero : N → Bool := by
  intro n
  cases n
  -- case Z
  exact true
  -- case S
  exact false
```

Recall that `match` tactic allows us to specify the cases, we can also use `match` to do so:
```lean
def Eqzero2 : N → Bool := by
  intro n
  match n with
  | N.Z   => exact true
  | N.S _ => exact false
```
`N.S _` means once a term is beginned with `N.S _`, then return `false`.


## Dedekind-Peano

We can prove some properties of `Nat` in Lean 4, which can be shown by self-defined type `N`. 

### Cases

`0` is not be a successor of any other `n : Nat`. We see this by the following:
```lean
open N
theorem TZInj : ∀ (n : N), Z ≠ S n := by
  intro n
  intro h
  /-
  n : N
  h : Z = n.S
  ⊢ False
  -/
  cases h
```
`cases h` attempts to decompose the equation `h`, while `Z` and `S n` are built by different constructors of the inductive type `N`, Lean can immediately determine that this equality is impossible. This is a consequence of the fact that constructors of an inductive type are disjoint. 

### Injection

Recall the definition `injective` defined before, we shall prove that `Nat.suss` is injective, and similarly by `N.S`:
```lean
theorem TSucc : injective S := by
  intro n
  intro m
  intro h
  injection h
```
where `injection` is a tactic that if you have an equality where the both sides have the same constructor, it extract a new hypothesis of an equality of the inputs.

### noConfusion

`noConfusion` principle formalizes the fact that:
- the different constructors of an inductive type are distinct
- they are injective when applied to arguments

It is essentially a function receives an unvalid equality and return `False`.

```lean
theorem TSuccInjAlt : injective S := by
  intro n
  intro m
  intro h
  exact N.noConfusion h id
```

## Induction

We now introduce an important tactic `induction`. If `x` is a variable of inductive type, then `induction x` applies induction on `x` to the main goal, where the goal is splitted into the cases of constructors.
```lean
theorem TInd {P : N → Prop} (h0 : P Z) (hi : ∀ (n : N), P n → P (S n)) : ∀ (n : N), P n := by
  intro n
  induction n
  -- case Z
  exact h0
  -- case S
  rename_i n hn    -- n : N  and  hn : P n
  -- ⊢ P n.S
  exact (hi n) hn
```

To apply the indcutive assumption, we may use `rw [ih]` where `ih` is the inductive assumption. Or, if `ih` is a function type, we may use `exact`, `apply` or `calc`.

## Recursion

Recursion allows us to define functinos in terms of simpler instances of themselves. In math, addition and multiplication are defined bu recursion on natural numbers.

### Maximum

We can define $max(m, n)$ function by recursion:
```lean
def max : N → N → N := by
  intro n m
  match n, m with
  | Z, m => exact m     -- if n=0, then m must be the maximum
  | n, Z => exact n     -- if m=0, then n must be the maximum
  | S n, S m => exact S (max n m)
```
For `S n, S m => exact S (max n m)`, it means if both of them are a successor of another `N`(so that they are not `Z`), then we compare `n` and `m`, and then return the successor of the larger one.

### Minimum

We can define $min(m, n)$ function by recursion:
```lean
def min : N → N → N := by
  intro n m
  match n, m with
  | Z, _ => exact Z     -- if Z is here, then Z must be the minimum
  | _, Z => exact Z     
  | S n, S m => exact S (min n m)  -- Recursion
```
`_` means "regardless of the another number".

### Addition

```lean
def Addition : N → N → N := by
  intro n m
  cases n with
  | Z => exact m             -- if n = Z, then n + m = m
  | S n => exact S (Addition n m) -- (n + 1) + m = (n + m) + 1, which is S (n + m)
```
so that the sum `n + m` is `n` times of successor of `m`. We can also assign a symbol for function `Addition n m` by
```lean
notation : 65 lhs:65 " + " rhs:66 => Addition lhs rhs
```

**Fibonacci Sequence**

We can define the Fibonacci function recursively:
```lean
def Fib : N → N := by
  intro n
  match n with
  | Z => exact Z           -- F(0) = 0
  | S Z => exact (S Z)     -- F(1) = 1
  | S (S n) => exact Addition n (S n) -- F(n+2) = F(n) + F(n+1)
```

### Multiplication 

Similarly,
```lean
def Multiplication : N → N → N := by
  intro n m
  cases n with
  | Z => exact Z    -- If n = Z, then Z * m = Z
  | S n => exact Addition (Multiplication n m) m
```
where `| S n => exact (Multiplication n m) + m` means that if `n` is not `Z`, then the product is defined as the sum of `m` and the product of the predecessor of `n` and `m`.

And hence, we can define the factorial:
```lean
def Fact : N → N := by
  intro n
  cases n with
  | z => exact (s z)  -- 0! = 1
  | s n => exact Multiplication (s n) (Fact n)  -- (n+1)! = (n+1) * n!
```

## Decidable Equality

Recall that `DecidableEq` is a type class in Lean 4 that it has an specialized algorithm to dertermine whether the elements in the type are equal. `DecidableEq` has two constructors: `isTrue` and `isFalse`, which requires a proof of equality holds and equality not holds, respectively.

Since `N` is an inductive type, we can define a recursive procedure to determine whether two values of type `N` are equal, and so that `N` is of type class `DecidableEq`.

```lean
def instDecidableEqN : DecidableEq N := by
  intro n m
  match n, m with
    | Z, Z => exact isTrue rfl
    | Z, S _ => exact isFalse (by intro h; cases h)
    | S _, Z => exact isFalse (by intro h; cases h)
    | S n, S m => 
      match instDecidableEqN n m with
        -- h0 : n = m
        | isTrue h0 => exact isTrue (congrArg S h0)
        -- h0 : ¬n = m
        | isFalse h0 => exact isFalse (fun h1 => N.noConfusion h1 (fun h2 => h0 h2)) -- ⊢ ¬n.S = m.S
```
For `| Z, S _ => exact isFalse (by intro h; cases h)`, we prove that the equlity not holds by `cases h`, which, as mentioned, inspect the contructor of the both elements and find that they are different.

For `S n, S m`, we enter the recursion and have two cases:
- It is true if `n = m`, by `congrArg` which is Congruence of Arguments and state that if `a = b` then `f a = f b` by `rfl`.

    ```lean
    #print congrArg
    /-
    theorem congrArg.{u, v} : ∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂ :=
    fun {α} {β} {a₁ a₂} f h => h ▸ rfl
    -/
    ```

- It is false if `¬n = m`, by:
  - `fun h1 =>`: It is same to `intro h1` where `h1 : n.S = m.S`. And, we need to prove `False` by `h1` and `h0`
  - By applying `N.noConfusion h1`(as `n m : N`), it returns a goal of `n.S = m.S`. Once we provide it, it returns `False`
  - `fun h2 =>`: means `h2 : n = m`, and we sub `h2` into `h0` so that `False` is produced.

  That means we recursively define $n \neq m$ by stating that their precedessors are not equal.


## Further Discussion

We know that $0$ and $1$ is the identity element of addition and multiplication, respectively. Let denote `one` as the successor of `Z` by
```lean
def one : N := S Z
```