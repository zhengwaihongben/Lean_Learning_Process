# Lean

**Lean** is an interactive theorem prover based on Calculus of Constructions. Its underlying logic is Dependency Type Theory.

# Dependency Type Theory (DTT)

The underlying logic of **Lean**.

## Formal System

A formal system is an abstract structure and formalization of an axiomatic system used for deducing. A formal system consists of two componets:
- Formal Language: This is a set of well-formed formulas, which are strings of symbols from an alphabet, formed by a formal grammar 
- Deductive system, deductive apparatus, or proof system, which has rules of inference that take axioms and infers theorems
Every deduction in a formal system must be valid under the deductive system.

## Type System

Type system is a formal system that represents mathematical objects, proposition and proof as typed *terms* and uses *type* checking to determine what is valid. Every expression has an associated *type*.

In set theory, the most foundamental relation is *belong to*: `x \in A`, while in type theory, it is *type ascription*: `x : A` which means that `x` is a term of the type `A`. Type specifies what kind of thing an expression is and how it may be used. 

In type system, proving a proposition is actually constructing a term that satisfies the type from the proposition. `Propositions are types, proofs are terms.` 

- Formal Language of Type System:

    Types, variables, determiners, etc.

- Deductive System of Type System: 

    The rules of how to construct valid types and terms.

### Universe Levels

A level system of the types in order to prevent contradictions such as *Russell's Contradiction*. The type of `Type` is `Type 1`, and the type of `Type 1` is `Type 2`. There are infinite levels of universes.
```lean
Type : Type 1
```
**Lean** uses `Sort u` to represent all universes. The universe of all propositon is `Sort 0`, the universe of all `Type` is `Sort 1`, and so on.

## DTT

Dependency Type Theory is a type theory that allows the types be depend on values. A type itself can also be a parameter, and the definition of a type can depend on values.

The properties of **DTT** allows that some precise mathematical definitions can be expressed by **Lean**.


# Basic

## Note

The notes in lean are typed by
- Single line note: 
  ```lean
  -- This is a single line note
  ```
- Multiple lines note:
  ```lean
    /-
    This is a 
    multiple
    lines note
    -/
  ```

## Typing Math
The mathematical symbols in Lean all are all typed by the abbreviation begined with `\`. Users can find the table of the abreviation by
```
Ctrl + Shift + P
Show Unicode Input Abbreviations
``` 

## Types

Lean involves some basic types, which are available without mathlib4.

| Type | Explanation | Example |
|---|---|---|
| `Nat` | National Numbers |  |
| `Int` | Integers |  |
| `Float` | Float/Decimals |  |
| `Char` | Characters | `'a'` |
| `String` | String | `"hello"` |
| `List type` | List with elements of type `type` | `[1, 2, 3] : List Nat` |
| ... | ... | ... |

## Checking types

The command `#check` is used to check the type of an object. 
```lean
#check 23
-- 23 : Nat

#check -4
-- -4 : Int

#check "true"
-- "true" : String

#check true
-- Bool.true : Bool

#check Nat
-- Nat : Type

#check Type
-- Type : Type 1
```
Note that for a positive integer, lean first regards it as a national number, instead of integers.

## Define constants

The command `def` is used to declare a new object with a certain type and value. In terms of constant, once a constant is defined, it can be invoked afterward. The syntax is:
```lean
def name : type := value
```
For example:
```lean
def weight : Float := 73   
-- defining a constant called "weight", and its type and value are "Float" and 73
#check weight
-- weight : Float

def P1 : Bool := false
#check P1
-- P1 : Bool
```
We can also declare new constant for types
```lean
def α : Type := Nat    
-- This define a constant called "α" with type "Type", and its value is "Nat"
#check α
-- Type
```

## Evaluate Values

The command `#eval` is used to evaluate a given expression. The syntax is:
```lean
#eval expression
```
One can evaluate the expressions by invoking constants defined.
```lean
#eval 11 + 12
-- 23

def weight : Float := 73
#eval weight
-- 73.800000
-- #eval also shows the value of a constant

def P1 : Bool := false
#eval P1
-- false
```

## Supplement: Cartesian Products

The Cartesian Products in lean are the types of the form: `A × B`, where `A` and `B` are types and `×` can be typed by `\times`. The terms in a Cartesian Product `A × B` are the ordered pairs `(a, b)` where `a` and `b` are the terms of `A` and `B`, respectively.
```lean
#check (3, -5)
-- (3, -5) : Nat × Int

def ab : Nat × Nat := (3, 5)
#eval ab
-- (3, 5)

#check (true, 'b', 4)
-- (true, 'b', 4) : Bool × Char × Nat
```

## Defining Functions

`def` can also define functions, with the syntax:
```lean
def name (parameter : type) : type_return := function
```
where `(parameter : type)` declare the symbol and type of parameter, `type_return` is the type of output returned, and `function` is the form of functions. Multiple parameters are allowed. A function can be invoked by `name p_1 p_2 ...`, where the order of `p_i` should be aligned with that in definition.

For example:
```lean
def add5 ( x : Int ) : Int := x + 5
#eval add5 9
-- 14
#check add5
-- add5 (x : Int) : Int
```
If the types of some parameters are same, then they can be written as `(p_1 p_2 : Type)`.

### fun

Another way to define a function is:
```lean
def name : type1 → type2 := fun parameter => funciton
```
where `type1` and `type2` are the types of input and output. For example:
```lean
def double : Nat → Nat :=
  fun x => x + x
```
This is sometimes useful.

### Nested functions/Compose

Functions can also be an input of another one. For example:
```lean
def dotwice (f : Int → Int) (x : Int) : Int :=
  f (f x)

def add5 ( x : Int ) : Int := x + 5

#eval dotwice add5 4
-- 14
```
Note that the type of parameter of the function nested should be aligned with that in its definition.

Moreover, the composite functions can be defined. In general:
```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```
where `α β γ` are the types of of the parameters, and it is supposed that `g` and `f` are defined. For example:
```lean
def square_int ( x : Int ) : Int := x ^ 2
def add5 ( x : Int ) : Int := x + 5

def compose (g : Int → Int) (f : Int → Int) (x : Int) : Int :=
  g (f x)

#eval compose add5 square_int 5
-- 30
```

## Local Definition

Lean also allows users to introduce local definitions by `let` keyword. A local definition is defined within an expression or a function. Syntax:
```lean
let name := t_1 ; t_2
```
where `t_1` is the value and `t_2` is an expression involving `name`. For example:
```lean 
#eval let y := 7 ; y * y
-- 49

def twice_double (x : Nat) : Nat :=
  let y := x + x
  y * y
#eval twice_double 3
-- 36
```

### Chained let

`let` can be used consecutively so that the later `let` can invoke the parameters in the preivous: 
```lean
#eval let y := 2 + 3; let z := y + y; z * z
-- 100
```

### Variable and Section

Lean provide `variable` and `section` for boilerplate, which are syntactic sugar for that if there is a variable invoked repeatedly, users do not need to declare it everytime by `variable`.

For instance:
```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```
We need to declare the types of the variables `α β γ` in every definition, which is redundant. `variable` allow us to declare them in advanced:
```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```
Moreover, we can also declare functions by `variable`:
```lean
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
```
The command `#print` shows the whole definition of an object.
```lean
#print compose
/-
def compose : (α β γ : Type) → (β → γ) → (α → β) → α → γ :=
fun α β γ g f x => g (f x)
-/
```
The application of a `variable` last until the end of the documnet. `section` command is used to set up a domain for the application of `variable`. Syntax:
```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```
`section` command allows nested structures. 


## Namespace

`namespace` sets up a domain for the names. Syntax:
```lean
namespace name_of_space
def v_1 : Nat := 5
#check v_1 
-- name_of_space.v_1 : Nat
end name_of_space

#check v_1
-- error
```
In the above example, the variable `v_1` is only legal within the space `name_of_space`. Meanwhile, a namespace must have a name, unlike `section` which does not always needed to be assigned. 

After the end of a namespasce, we can activate it again by `open`
```lean 
open name_of_space
...
```
while it does not end until the current block ends. Thus, we can bound `open` command by `section`:
```lean
section 
  open name_of_space
  ...
end
```

## Nature of Dependent Type Theory

The essence of DTT is that 

> Types can depend on parameters, and the types can be computed.

For instance
```lean
def cons1 (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as
```
- `(α : Type)`: `α` is the first parameter of type `Type`, so you have to input a concrete type such as `Nat`, `Bool`.
- `(a : α)`: `a` is the second parameter of type `α`, so that the type of `a` depends on the first parameter
- `(as : List α)`: `as` is the third parameter of type `List α`, which is a list consist of elements of type `α`. 
- `: List α`: `cons` is a function with inputs of type `List α`
- `:= List.cons a as`: `List.cons` is a functions of Lean standard library, which insert `a` in the beginning of `as`.

```lean
#eval cons1 Nat 2 [1,2,3]
-- [2, 1, 2, 3]
```

We say that types can depend on parameters because the types of an object vary with the parameters input. 

```lean
#check cons1 Nat
-- cons1 Nat : Nat → List Nat → List Nat
#check cons1 Bool True
-- cons1 Bool (decide True) : List Bool → List Bool
```
where the type of `cons1 Nat` is `Nat → List Nat → List Nat`, which is of type `Type`
```lean
#check Nat → List Nat → List Nat
-- Nat → List Nat → List Nat : Type
```

## @ command

`@` command make the implicit parameters be explicit. Recall that there are three ways to assign the types
- `(x : α)`: explicit parameter that the users must assign a type.
- `{x : α}`: implicit parameter that lean would determine the type.
- `[x : α]`: Lean would find by itself

Sometimes, if lean could not determine the type, or you want to assign the type, `@` is used. For instance
```lean 
#check List.cons
-- List.cons.{u} {α : Type u} (head : α) (tail : List α) : List α
#eval List.cons 2 [1]
-- [2, 1]
#eval @List.cons Nat 2 [1]
-- [2, 1]
```
The first parameter of `List.cons` is actually a value of type `u`, and `#eval @List.cons Nat 2 [1]` imposes the type `Nat` on `2`.

## Goal

"Goal" is one of the core concept in Lean. It is basically the statement that you need to prove now. In InfoView, a goal is represented by `⊢`. The goal can be switched by tactics. Tactics are the commands that describe how to build such a proof. 

For a proposition to be proven: `theorem my_thm : P → Q := by ...`, the initial goal is `P → Q`, and then we eliminate the goal by tactics, such as substituting a goal into different smaller sub-goals.

When InfoView shows that `No goals`, we have proven the proposition.


## Sigma Types

Sigma Type is a special product(Cartesian) that put an object and something relied on the object togather. 

The syntax sugar of Sigma Type is: `Σ a : α, β a` (`Σ` is typed by `\Sigma`) where `β` is a function whose type depends on `a`. This structure packs a value `a` and a type `β a` dependent on the value togater to `⟨a, b⟩` (typed by `\langle, \rangle`).

## Quantifiers in Lean

### Universal Quantifier

$\forall x P(x)$ means that for all $x$ such that $P(x)$ holds. 

We can define $\forall$ in Lean by "dependent function type", which is a type that the type returned depends on the value input. The basic syntax of dependent function type is: `(x : α) → β x`, where `β` is a function of type `α → Type` that receive a value `x` and then return a type `β x`.

$\forall$ in lean relies on the syntax sugar of the dependent function type, where in `(x : α) → β x`, `β` itself also relies on `x`. 

$\forall x P(x)$ in lean is represented by `∀ x : α, P x`. To prove `∀ x : α, P x`, we need to provide a function receiving `x` and returning that `P(x)` holds.

### Existence Quantifier

$\exists$ in lean is defined by "inductive type", which is a type constructing new elements by finite steps with a group of basic elements.
