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
