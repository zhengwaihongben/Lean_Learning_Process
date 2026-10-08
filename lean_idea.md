# Idea of Lean

**Lean** is an interactive theorem prover based on Calculus of Constructions. Its underlying logic is Dependency Type Theory.

## Dependency Type Theory (DTT)

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

Philosophy of "Propositions as types":
- 命題 `p` 是一個數據類型，証明 `t` 是這個類型的對象。只有構造出這個對象，命題才為真。
- 把命題 p 關聯到一個類型，如果 `p` 為假，這個類型就是空的（沒有元素）；如果 `p` 為真，這個類型就至少有一個元素。能寫出一個項 `t : p`，就説明這個類型非空，即命題為真。

### Universe Levels

A level system of the types in order to prevent contradictions such as *Russell's Contradiction*. The type of `Type` is `Type 1`, and the type of `Type 1` is `Type 2`. There are infinite levels of universes.
```lean
Type : Type 1
```
**Lean** uses `Sort u` to represent all universes. The universe of all propositon is `Sort 0`, the universe of all `Type` is `Sort 1`, and so on.

## DTT

Dependency Type Theory is a type theory that allows the types be depend on values. A type itself can also be a parameter, and the definition of a type can depend on values.

The properties of **DTT** allows that some precise mathematical definitions can be expressed by **Lean**.