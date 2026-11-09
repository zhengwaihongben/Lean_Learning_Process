# Choice

A type is *nonempty* if it contains at least one element, but this existence is not neccessarily constructive.

A type is *inhabited* if we can specify a concrete default element, making it more useful in computational contexts.

This distinction becomes particularly significant when comparing constructive and classical reasoning. In constructive logic, knowing that a type is nonempty does not guarantee that we can extract an element from it, whereas in classical logic, the axiom Classical.choice allows us to select an element from a nonempty type, thereby making it inhabited.

## Inhabited Types

The inhabited `α` typeclass ensures that the type `α` has a designated element, known as `default : α`. 
```lean
#print Inhabited
/-
class Inhabited.{u} (α : Sort u) : Sort (max 1 u)
number of parameters: 1
fields:
  Inhabited.default : α
constructor:
  Inhabited.mk.{u} {α : Sort u} (default : α) : Inhabited α
-/
```
which means `Inhabited` is a typeclass with a single parameter `α`, and a constructor `Inhabited α`. `fields:  Inhabited.default : α` means if you want to claim `α` is inhabited, you must provide an element `default` of type `α`.

The constructor `Inhabited α` receives a type `α` and a term `default : α`, and then returns a proof `Inhabited α`.

A *typeclass* is a special kind of structure that defines a set of properties or operations that a type can possess. To define a specific instance of a type class, we use the `instance` or `def` keywords. The general syntax is:
```lean
instance name : Inhabited type_name := { default := term}
```
For example: 
```lean
instance InBool : Inhabited Bool := { default := true }
```
defines a default to `Bool`. We can give a default value for `Bool` if necessary.


## Nonempty

The `Nonempty` type is an inductive predicate that asserts the existence of at least one element in a given tyep. 
```lean
#print Nonempty
/-
inductive Nonempty.{u} : Sort u → Prop
number of parameters: 1
constructors:
Nonempty.intro : ∀ {α : Sort u} (val : α), Nonempty α
-/
```
`Nonempty.intro` is the only constructor that if you provide an element `a : α`, you can prove `Nonempty α`. In other words, `Nonempty α` is true if there exists at least one instance of `α`. 

For instance
```lean
theorem TNEBool : Nonempty Bool := Nonempty.intro true
```
we prove that `Bool` is nonempty since we provide `true : Bool`.

One more point is that if a type is inhabited, then it is also nonempty:
```lean
def InhabitedToNonempty {A : Type} : Inhabited A → Nonempty A := by
  intro h
  exact Nonempty.intro h.default
```
which directly provide the defaclt of type `A`.

## Choice

It is not alwayss true for `Nonempty A → Inhabited A`. If we know that a type is nonempty, we can use axiom of choice `Classical.choice` to obtain a term of type `A`, while this term is noncomputable.
```lean
#print Classical.choice
-- axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α
```

Consider the following function
```lean
noncomputable def NonemptyToInhabited {A : Type} : Nonempty A → Inhabited A := by
  intro h
  have a : A := Classical.choice h
  exact Inhabited.mk a
```
This function demonstrates how a proof of nonemptiness can be converted into a proof of inhabitation. `Nonemptye A` assets the existence of at least one element in the type `A`, and it uses `Classical.choice` to extract `a : A`. And, the extracted element is then used to construct a proof of inhabitation using `Inhabited.mk`, which asserts that `A` has a predefined default element.

Note that this function is marked as `noncomputable`. 

### Choose

`Classical.choose` is a function from classical logic that enables the selection of an element satisfying a give predicate. Especially, for an existential predicate `∃ a : A, P a`, `Classical.choose` returns one such element `a` for which `P a` is true. 

We can also use `Classical.choose_spec` to obtain the proposition that `a` satisfies, such as `P a`.

For example:
```lean
theorem TCarNonempty {A : Type} : Nonempty A ↔ ∃ (a : A), a = a := by
  apply Iff.intro
  -- Nonempty A → ∃ a, a = a
  intro h
  apply Exists.intro
  exact rfl
  -- ∃( a, a = a) → Nonempty A
  have a : A := Exists.choose h
  exact Nonempty.intro a
```