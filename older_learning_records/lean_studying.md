# Lean

**Lean** is an interactive theorem prover based on Calculus of Constructions. Its underlying logic is Dependency Type Theory.

## Dependency Type Theory (DTT)

The underlying logic of **Lean**.

---
### Formal System

A formal system is an abstract structure and formalization of an axiomatic system used for deducing. A formal system consists of two componets:
- Formal Language: This is a set of well-formed formulas, which are strings of symbols from an alphabet, formed by a formal grammar 
- Deductive system, deductive apparatus, or proof system, which has rules of inference that take axioms and infers theorems
Every deduction in a formal system must be valid under the deductive system.

---
### Type System

Type system is a formal system that represents mathematical objects, proposition and proof as typed *terms* and uses *type* checking to determine what is valid. Every expression has an associated *type*.

In set theory, the most foundamental relation is *belong to*: `x \in A`, while in type theory, it is *type ascription*: `x : A` which means that `x` is a term of the type `A`. Type specifies what kind of thing an expression is and how it may be used. 

In type system, proving a proposition is actually constructing a term that satisfies the type from the proposition. `Propositions are types, proofs are terms.` 

- Formal Language of Type System:

    Types, variables, determiners, etc.

- Deductive System of Type System: 

    The rules of how to construct valid types and terms.

**Universe Levels**: 

A level system of the types in order to prevent contradictions such as *Russell's Contradiction*. The type of `Type` is `Type 1`, and the type of `Type 1` is `Type 2`. There are infinite levels of universes.
```lean
Type : Type 1
```
**Lean** uses `Sort u` to represent all universes. The universe of all propositon is `Sort 0`, the universe of all `Type` is `Sort 1`, and so on.

---
### DTT

Dependency Type Theory is a type theory that allows the types be depend on values. A type itself can also be a parameter, and the definition of a type can depend on values.

The properties of **DTT** allows that some precise mathematical definitions can be expressed by **Lean**.


# Basic Syntax

## Notes
A single line note is: 
```lean
-- This is a single line note.
```
A note of multiple lines is:
```lean
/-
This is a note of multiple lines.
-/
```


## Typing Math
The mathematical symbols in Lean all are all typed by the abbreviation begined with `\`. Users can find the table of the abreviation by
```
Ctrl + Shift + P
Show Unicode Input Abbreviations
``` 

## Basic Types

**Lean** involves some basic types, which are available without mathlib4.

| Type | Explanation | Example |
|---|---|---|
| `Nat` | National Numbers |  |
| `Int` | Integers |  |
| `Float` | Float/Decimals |  |
| `Char` | Characters | `'a'` |
| `String` | String | `"hello"` |
| `List type` | List with elements of type `type` | `[1, 2, 3] : List Nat` |
| ... | | |

Mathlib4 provides numerous types.


## Commands

Commands are the words started with `#` and followed by an experssion.
```lean
#keyword expression
```
The commands only return results, and do not change the enviroment.

- **check**

    The type of an object `A` is shown by `#check`. For example:
    ```lean
    #check 3
    -- Nat
    #check [2, 5, 7.8, 0]
    -- [2, 5, 7.8, 0] : List Float
    ```

- **eval**

    The value of an expression can be calculated by `#eval`
    ```lean
    #eval 2 + 3
    -- 5
    ```

- **print**

    It shows the type and the definition of an object
    ```lean
    #print Int
    /-
    inductive Int : Type
    number of parameters: 0
    constructors:
    Int.ofNat : Nat → Int
    Int.negSucc : Nat → Int
    -/
    ```

- **reduce**

    It uses the deductive rules of Lean to simplify an expression
    ```lean
    #reduce 2 + 6
    -- 8
    ```

Moreover, `import` and `open` are also considered as commands.
- **import**

    It loads a certain Lean module to the current environment so that the users can invoke the functions of the module. It must by placed in the beginning of a document.
    ```lean
    import ...
    ```
- **open**

    The definitions of Lean usually stored in namespace such as `Nat.add`, `Real.sqrt`. `open` allows users invoke the definitions directly and not to type the complete prefix.
    ```lean
    import Mathlib.Data.Real.Basic
    open Real
    #check sqrt
    -- sqrt : ℝ → ℝ
    ```


## Declarations

The syntax elements that add a paramount content in Lean environment, such as adding a new definition.

Commands, declarations are collectively known as **Syntax Elements**.


### def

Define a variable, function, type, etc. The syntax is
```lean
def name ( parameter : type_p ) : type_name := term
```

- `name`: the name of the definition
- `parameter`: the input of the definition. Multiple parameters are allowed.
- `type_p`: the type of the parameter.
- `type_name`: the type of the output of the definition. Lean can determine that if the users do not provide.
- `term`: the content/form of the definition

Some useful `def`:

1. Variable
    ```lean
    def x : Nat := 3
    #eval x + 2     -- 5
    ```
2.  Function
    ```lean
    def add3 (a b c : Nat) : Nat :=
        a + b + c

    def time2 ( a : Nat )( b : Float) :=
        a * b
    -- the type of the result can be neglected
    ```
3. Implicit Parameters

    The parameters bounded by `{}` are implicit, which lean determines by context
    ```lean
    def identity (α : Type) (x : α) : α := x
    #eval identity 3      -- 3 : Nat
    ```
    where `α` is a parameter of types.

### example
`example` is a command that the content of which do not preserve in the environment, and it does not need a name.
```lean
example (parameter : type_p) : type := term
```

### theorem
`theorem` declares a proposition and provides a correspoding proof. Furthermore, `lemma` is totally same to the former one instead of the name.
- Terms mode
    ```lean
    theorem name (parameter : type_p) : proposition := proof
    ```
    The type of `proposition` must be `Prop`.
- Tactic mode
    ```lean
    theorem name (parameter : Prop) : Proposition := by
        tactic 1
        tactic 2
    ```
    After `by`, lean enters an interactive proof state. Each tactic interacts with the state by introducing hypothesis, applying theorem, etc. Seen in the part of **tactic**.

## Tactic
Tactic elements only appear after `by`. Each tactic element is essentially a metaprogram, which reads the current proof statem handles the goal of proof, and then generate a new proof state. The new state will be examined by the kernel of lean.

### Basic Tactic
```lean
intro h
exact h
apply h
rw [h]
simp
constructor
cases b
induction n
```
- **intro**
    
    Introduce the hypothesis of the outest universal quantifer or implication, and change them to the hypothesis or the local variables.
    ```lean
    intro h1 h2 ... hn
    ```
    User can also introduce multiple variables.

- **exact**

    Finish the goal by a term which has the same type with the goal, and let the kernel of lean examine that.
    ```lean
    example (P Q : Prop) (hp : P) (h : P → Q) : Q := by
        exact h hp
    ```

- **apply**

    Take an established conclusion and replace it to the hypothesis of the goal
    ```lean
    example (P Q : Prop) (hp : P) (h : P → Q) : Q := by
    apply h
    -- goal turns to ⊢ P
    exact hp
    ```

- **rw**

    `rw` is the abbreviation of rewrite. It turns a certain expression in the goal or hypothesis to another one by an equivalence.
    ```lean
    rw [h]
    ```
    where `h` is a proposition, and lean finds the equivalence of `h` from the goal or hypothesis. For instance
    ```lean
    example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
    rw [h1, h2]
    /-
    rw [h1]: the goal changes from a = c to a = b by the statement of h1
    rw [h1]: the goal changes from a = b to b = c by the statement of h2
    -/
    -- goal turns to c = c
    rfl
    ```

- **rfl**

    The abbreviation of reflexivity. It turn off the goals of the form `a = a`.
    ```lean
    example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
    rw [h]
    rfl
    ```

- **assumption**

    Find a hypothesis in local context that is definitionally equal to the goal. Once the hypothesis is found, the proof finishes and let the kernel examine it.
    ```lean
    example (P Q : Prop) (hp : P) (hq : Q) : Q := by
        assumption
        -- to prove Q
        -- find hq that has the same type to Q by assumption
    ```
    ```lean
    example (h : 4 = 4) : 2 + 2 = 4 := by
        assumption
    ```
- **simp**

    simplify the expression

- **constructor**
    
    Seperate a disjunction `\land`

    ```lean
    example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
    constructor
    · exact hp  -- 第一個子目標：證明 P
    · exact hq  -- 第二個子目標：證明 Q
    ```
    `·` is for concentrating a subgoal.

- **left / right**

    To determine which side of a conjunction is being proved. 
    ```lean
    example (P Q : Prop) (hp : P) : P ∨ Q := by
        left        -- 目標變為 ⊢ P
        exact hp    -- 用假設 hp 完成證明
    example (P Q : Prop) (hq : Q) : P ∨ Q := by
        right       -- 目標變為 ⊢ Q
        exact hq
    ``

- **use**

    To prove the existence `\exists`. 
    ```lean
    example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
        use 5 / 2
        norm_num
    ```
    `norm_num` is to calculate automatically.

- **cases**

    seperate a main goal into several cases.

    **rcases**

    it is an advanced version of **cases**

- **induction**

    for mathematical induction. The inductive hypothesis is generaed automatically. Usually used with `with`, `|`, and `=>`. `with` is to pointed out the cases, `|` is to seperate different cases, and `=>` means that if the case matches, then execute the following contents.  
    ```lean
      induction n with
        | zero => rfl
        | succ n ih =>
            rw [Nat.add_succ, ih]
    ```

### Tactic Combinators
The elements combining multiple tactics.
| Combinators | Functions |
| --- | --- |
| `t1; t2` | Execute `t1` first, and then `t2` to the stuff generated |
| `t1 <;> t2` | Execute `t2` to all stuff generated by `t1` |
| `try t` | Execute `t`, and neglect if it falses |
| `repeat t` | Execute `t` repeatedly until false |
| `first \| t1 \| t2 ...` | Execute `t1`, and then `t2` until true |
| `all_goals t` | Execute `t` to all goals |

Attribute

Notation
