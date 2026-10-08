# Basic Reasoning

## Propositions as Types

In usual mathematics, we states a proposition $P$, and then we start a series of reasoning called "Proof". 

While in Lean, we treat the propositions `p : Prop` as a type, and the proof of `p` as a specific term of the type, which means that if `t : p`, then `t` is a proof of `p`.

This is essentially the idea of Dependent Type Theory.

Philosophy of "Propositions as types":
- 命題 `p` 是一個數據類型，証明 `t` 是這個類型的對象。只有構造出這個對象，命題才為真。
- 把命題 p 關聯到一個類型，如果 `p` 為假，這個類型就是空的（沒有元素）；如果 `p` 為真，這個類型就至少有一個元素。能寫出一個項 `t : p`，就説明這個類型非空，即命題爲真。

### Constructors

Lean provides basic logical constructors to define new propositions based on established propositions. We have and`∧`, or`∨`, not`¬`, and implies`→`.
```lean
def p : Prop := 2=2
def q : Prop := 3=3
#check p ∧ q
-- p ∧ q : Prop
```

### Theorem `theorem`

Lean provides the command `theorem` to define a proposition(type) and establish its proof(term). The syntax is:
```lean
theorem name (parameter : type) : proposition := proof
```
The part after `:=` is basically constructing a term of `proposition`. Lean inspects the type of `proof` and adopts the theorem once the type of `proof` is same to `proposition`.