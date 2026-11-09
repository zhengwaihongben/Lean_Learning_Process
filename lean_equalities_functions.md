# Equalities

In the following, we always assume that
```lean
variable (A : Type)
variable (a b c d : A)
variable (P : A → P)
```

Equalities, typed by `Eq`, is a type. 
```lean 
#check Eq
-- Eq.{u_1} {α : Sort u_1} : α → α → Prop
#print Eq
/-
inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop
number of parameters: 2
constructors:
Eq.refl : ∀ {α : Sort u_1} (a : α), a = a
-/
#print Eq.refl
-- constructor Eq.refl.{u_1} : ∀ {α : Sort u_1} (a : α), a = a
```
It is an inductive type with a unique constructor `Eq.refl`, which receives two terms of the same type and return a proposition. The type of `Eq.refl` is `∀ (a : α), a = a`. An equality can be type by either `Eq a b` or `a = b`.

The inequalities, similarly, is a type, typed by `Ne`. An inequality can be typed by either `Ne a b` or `a ≠ b`(`\neq`).
```lean
#print Ne
/-
@[reducible] def Ne.{u} : {α : Sort u} → α → α → Prop :=
fun {α} a b => ¬a = b
-/
```
that means `a ≠ b` is actually `¬(a = b)`, and defined by the negation of `Eq`.

## Reflexivity

The principle of reflexivity is thta every element is equal to itself. During a proof, we can use `Eq.refl a` to generate a goal of `a = a`. In short, if we have known that the goal is established, we can use `exact rfl` to finish. In addition, the kernel conducts the definitional equality, which automatically simplifies the both sides of `=`, and then check the equality. `rfl` is a syntax candy of `Eq.refl`.
```lean
example (2 4 : Nat) : 2+2 = 4 :=
    exact rfl
```
```lean
#check rfl
-- rfl.{u} {α : Sort u} {a : α} : a = a
```

## Symmetry

If we have `h : a=b`, we can derive `b=a` by using the symmetry of equality, which can be achieved by `Eq.symm h`. We can also type `Eq.symm h` in short by `h.symm`.
```lean 
example (h : a=b) : b = a :=by
    exaxt h.symm
```
```lean
#print 
/-
theorem Eq.symm.{u} : ∀ {α : Sort u} {a b : α}, a = b → b = a :=
    fun {α} {a b} h => h ▸ rfl
-/
```

## Transitivity

If we have `h1 : a=b` and `h2 : b=c`, we can derive `a=c` by the transitive property of equaltiy, which can be achieved by `Eq.trans h1 h2` or in short `h1.trans h2`.
```lean
example (h1 : a=b)(h2 : b=c) : a = c := by
    exact Eq.trans h1 h2
```
```lean
#check Eq.trans
-- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
```

## Rewrite

The tactic `rewrite [e]` applies the identity `e` into the current goal. For example that if we have `h : a=b`, then `rewrite [h]` replace all `a` in the goal to `b`(Or conversely). We can apply multiple equalities simultaneously by `rewrite [e1, e1, ..., en]`. 

We can replace the variables in the hypothesis by `rewrite [e1] at e2` where `e1` and `e2` are equalities. 

Furthermore, the syntax candy `rw [e]` first executes the function of `rewrite` and then tries to apply `rfl` to finish the proof: `rw = rfl ∘ rewrite`.
```lean
example (P : A → Prop)(a b : A) (h1 : a=b) : P b ↔ P a := by
  apply Iff.intro
  .
    intro h2
    rewrite [h1]
    exact h2
  .
    intro h3
    rewrite [h1] at h3
    exact h3
```

## Calc

`calc` command is for structured reasoning by chaining a sequence of equalities or inequalities. The syntax is:
```lean
calc
  expr_1 = expr_2 := justification_1
  _      = expr_3 := justification_2
  _      = expr_4 := justification_3
```
where `expr_i` are expression, `justification_1` are proofs that establish each equality of inequality, and `_` connects the steps. For example
```lean
example (h1 : a = b) (h2 : b = c) (h3: c = d) : (a = d) := by
  calc
    a = b := by rw[h1]
    _ = c := by rw[h2]
    _ = d := by rw[h3]
```

## Simp

`simp` tactic is similar to `rw`. It is an automated rewriting engine by searching all appropriate hypothesis, and finish the proof if the result is exactly the goal after simplification. 

We can also use `simp [def, statement]` to simplify `statement` based on the definition `def`.

# Types with meaningful equality

Usually, we use `=` to indicate that the two expression are equal. In Lean 4, we can use it to connect all types, but not all of them can be connected naturally. The interpretation and behavior of `=` depend on the structure of the specific type. 

## Decidable Equality

In Lean 4, there exists some algorithms to determine whether any two elements of a type are equal, where these types called said to have decidable equality. The algorithm is defined by `DecidableEq` typeclass.
```lean
#print DecidableEq
/-
@[reducible] def DecidableEq.{u} : Sort u → Sort (max 1 u) :=
    fun α => (a b : α) → Decidable (a = b)
-/
```
So basically `DecidableEq` is a function of types, which returns the algorithm of judging whether two terms of type type are equal. It relies on the type `Decidable`:
```lean
#check Decidable
-- Decidable (p : Prop) : Type
#print Decidable
/- 
inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
-/
```
`Decidable` judges the truth of an equality.

Some types have preset `DecidableEq`, such as `Nat`, `Int`, `String`.

## Equality in Prop

For `Prop`, equalities are defined by logical equivalence(iff). This is guaranteed by a built-in axiom `propext`, which states that:
```lean
#print propext
-- axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
```

Unlike the equalities of `Nat` or `Int`, the logical equivalence are generally undeciable, which mean determining whether two arbitrary propositions should be verified by human with `propext`.

For instance we want to state that `Q ∧ True) = Q `:
```lean
example {Q : Prop} : (Q ∧ True) = Q := by
    apply propext
    apply Iff.intro
    -- ⊢ Q ∧ True → Q
    intro h2
    exact h2.left
    -- ⊢ Q → Q ∧ True
    intro h3
    apply And.intro  -- seperate the disjunction
    -- ⊢ Q
    exact h3
    -- ⊢ True
    trivial
```

Furthermore, we can inspect which axioms are applied during the proof of a theorem `name` by `#print axioms`:
```lean
#print axioms name
```



# Functions

In Lean 4, a **function** is a relation that associates element of one type(domain) with a unique element of another type(codomanin). 

We first assume that
```lean
variable (A B C D : Type)
```
Recall that for given types `A` and `B`, the expression `A → B` is the type of all functions from `A` to `B`. In this context, `A` is called the domain, and `B` the codomain, where each element `f` of `A → B` is a function. In Math, you can consider the type `A → B` as a family of mappings from `A` to `B`.

For a certain term `a` of `A`, we write `f a` to apply `a` in `f`, which is the image of `a` under `f` and has type `B`
```lean
variable (f g : A → B)
variable (a : A)
#check f a
-- f a : B
```

### Equality

Recall we have proposition etensionality `propext`, which states that for the propositions, once `a ↔ b`, we have `a = b`. Similarly, we have function extensinoality `funext`, which is an axiom that if two functions with the same domain and codomain produce the same oupt for every input, then they are equal:
```lean
#print funext
/-
theorem funext.{u, v} : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g :=
fun {α} {β} {f g} h =>
  let eqv := fun f g => ∀ (x : α), f x = g x;
  let extfunApp := fun f x => f.liftOn (fun f => f x) fun x_1 x_2 h => h x;
  id (congrArg extfunApp (Quot.sound h))
-/
```
The core is that `∀ (x : α), f x = g x) → f = g`.

Conversely, if two functions are equalt, then they yield the same result for every input, which is called the congruence property of function. It is guaranteed by the axiom `congrFun`:
```lean
#print congrFun
/-
theorem congrFun.{u, v} : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g → ∀ (a : α), f a = g a :=
fun {α} {β} {f g} h a => h ▸ rfl
-/
```

They can be used to construct a proof:
```lean
example (A B: Type)(f g : A → B): (f = g) ↔ ∀ (a : A), f a = g a := by
  apply Iff.intro
  -- f = g → ∀ (a : A), f a = g a
  intro h
  intro a
  exact congrFun h a
  -- ∀( (a : X), f a = g a) → f = g
  intro h
  exact funext h
```
In fact, we can consider `funext` as proving set related propositions by discussing element-wise. To analog, if we want to prove $A = B$, we can discuss by
$$\forall x \in A, x \in B$$
and 
$$\forall x \in B, x \in A$$

### Composition

If we have `f : A → B` and `h : B → C`, then their composition `h ∘ f`(`\circ`) is a function of type `A → C`
```lean
variable (h : B → C)
#check h ∘ f
```
An important property of composition is associativity that for `f : A → B`, `g : B → C`, and `h : C → D`, we have `h ∘ (g ∘ f) = (h ∘ g) ∘ f`:
```lean
example (A B C D : Type)(f : A → B)(g : B → C)(h : C → D): h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  funext a
  rfl
```
where `funext a` turns the goal from an equality of functions into that of the images of functions, and then we use `rfl` to end since the kernel of Lean 4 deassembles the parentheses and inspect them.

### Identity functions

For any type `A`, we have the identity function `id`, which is of type `A → A`. It simply returns the input unchanged.
```lean
#print id
/-
@[implicit_reducible] def id.{u} : {α : Sort u} → α → α :=
fun {α} a => a
-/
```

By the definition, `id` returns receives an input of any type and then returns the input. In fact, `id` serves as a neutral element for function composition so that for any function `f : A → B`, we have `id ∘ f = f ∘ id`
```lean
example (A B : Type)(f : A → B) : (f ∘ id = f) ∧ (id ∘ f = f) := by
  apply And.intro
  -- ⊢ f ∘ id = f
  funext a -- ⊢ (f ∘ id) a = f a
  rfl
  -- ⊢ id ∘ f = f
  funext a
  rfl
```

We can explicitly specify the domain of `id` by using `@` before `id`. For example
```lean
#check @id Int
-- id : Int → Int
```

## Injections

### Injection

For a map or a function $f : A → B$, it is injective if for all $a_1, a_2 \in A$, $f(a1) = f(a2)$ implies that $a1 = a2$. We can define it by
```lean
def injective {A B : Type} (f : A → B) : Prop := ∀{a1 a2 : A}, (f a1 = f a2) → (a1 = a2)
```
which mean `injective` is a `Prop` of input `f : A → B`, which states that `∀{a1 a2 : A}, (f a1 = f a2) → (a1 = a2)`.

Note that once we define a definition, such as `injective`, we can use it as a building block. We can use `injective f` to declare a hypothesis or a goal that `f` is injective, instead of typing a chain of codes. For example:
```lean
example {A : Type} : injective (@id A) := by
-- ...
example (h1 : injective f) (h2 : injective g) : injective (g ∘ f) := by
```
Or, we can use `rw [injective]` while `injective` is in the goal, to decompose the goral into the definition of `injective`
```lean
example {A : Type} : injective (@id A) := by
  rw [injective] 
  -- change the goal from "injective id" tp "∀ a1 a2, id a1 = id a2 → a1 = a2"
  intro a1 a2 h 
  -- we can now introduce a1, a2 and h
  -- ...
``` 
It is similar to the following concepts.

### Monomorphism 單態射

In category theory, $f : A → B$ is a monomorphism if it is a morphism with left-cancellative, that mean for all $g_1, g_2: C → A$, $f \circ g_1 = f \circ g_2$ implies $g_1 = g_2$. In lean, we can define it in Lean 4 by:
```Lean
def monomorphism {A B : Type} (f : A → B) : Prop := ∀{C : Type}, ∀{g h : C → A}, f ∘ g = f ∘ h → g = h
```

### Left Inverse

We say that a function $f : A \to B$ has a left inverse if there exists a function $g : A \to B$ such that $g \circ f = id$. We can define it in Lean 4 by
```lean
def hasleftinv {A B : Type} (f : A → B) : Prop := ∃(g : B → A), g ∘ f = id
```

### An example: The identity

The identity is injective, a monomorphism and has a left inverse.
```lean
-- id is injective
theorem TIdInj : injective (@id A) := by
  -- we can turn call out the definition
  rw [injective]
  intro a1 a2 h
  /-
  A : Type
  a1 a2 : A
  h : id a1 = id a2
  ⊢ a1 = a2
  -/
  calc  -- build a chain of calculation
  a1 = id a1 := by exact rfl
  _ = id a2 := by exact h
  _ = a2 := by exact rfl
```
Note that we need to specify the type of input of `id` because the definition `injective` requires to specify that `f : A → B`.

```lean
-- id is a monomorphism
theorem TIdMon : monomorphism (@id A) := by
  rw [monomorphism]
  intro C g h h2
  /-
  A C : Type
  g h : C → A
  h2 : id ∘ g = id ∘ h
  ⊢ g = h
  -/
  calc
    g = id g := by exact rfl
    _ = id ∘ h := by exact h2
    _ = h := by exact rfl
```

```lean
-- id has a left inverse
theorem TIdHasLeftInv : hasleftinv (@id A) := by
  rw [hasleftinv]
  apply Exists.intro id   -- which means sub g = id
  exact rfl
```

## Surjections

### Surjection

A function $f: A \to B$ is surjective if for any $y \in B, \exists x \in A$ such that $f(x) = y$. We can define it in Lean 4 by
```lean
def hasrightinv {A B : Type}(f : A → B): Prop := ∀ (y : B), ∃ (x : A), f x = y
```

### Epimorphism 滿態射

In category theory, an epimorphism is a map $f : A \to B$ such that for $g_1, g_2 : B \to C$, $g_1 \circ f = g_2 \circ f$ implies that $g_1 = g_2$. We can define that by
```lean
def epimorphism {A B : Type} (f : A → B) : Prop := ∀{C : Type}, ∀{g h : B → C}, g ∘ f = h ∘ f → g = h
```

### Right Inverse

A function $f: A \to B$ has a right inverse if there esixts a function $g: B \to A$ such that $f \circ g = id$
```lean
def hasrightinv {A B : Type}(f : A → B) : Prop := ∃(g : B → A), f ∘ g = id
```

### An example: The identity

The identity is surjective, an epimorphism and has a right inverse.
```lean
-- id is surjective
theorem TIdSurj : surjective (@id A) := by
  rw [surjective]
  intro a
  apply Exists.intro a
  rfl
```

```lean
-- id is an epimorphism
theorem TIdEpi : epimorphism (@id A) := by
  rw [epimorphism]
  intro B g h h1
  calc
    g = g ∘ id := by exact rfl
    _ = h ∘ id := by exact h1
    _ = h := by exact rfl
```

```lean
-- id has a right inverse
theorem TIdHasrightinv : hasrightinv (@id A) := by
  rw [hasrightinv]
  apply Exists.intro id
  rfl
```

## Bijection

### Bijective

A function $f: A \to B$ is bijective if it is injective and surjective. We can define it in Lean 4 by
```lean
def bijective {A B : Type} (f : A → B) : Prop := injective f ∧ surjective f
```

### Isomorphism

In category theory, a function $f : A \to B$ is an isomorphism if there exists a function $g : B \to A$ such that $f \circ g = id$ and $g \circ f = id$. In Lean 4:
```Lean
def isomorphism {A B : Type} (f : A → B) : Prop := ∃ (g : B → A), g ∘ f = id ∧ f ∘ g = id
```

### An example: The identity 

The identity is bijective and an isomorphism

```lean
-- id is bijective 
theorem TIdBij : bijective (@id A) := by
  rw [bijective]
  apply And.intro
  exact TIdInj
  exact TIdSurj
```

```lean
-- id is an isomorphism
theorem TIdIso : isomorphism (@id A) := by
  rw [isomorphism]
  apply Exists.intro id
  apply And.intro
  rfl
  rfl
```