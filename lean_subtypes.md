# Subtypes

A **subtype** is a way to define a restricted entity of a given type by specifying a condition that the elements of this type must satisfy.For example in math, the even number is a subset of integers that satisfy $\exists k \in \Z, n = 2k$. Subtypes is similar to that.

A subtype of a type `A` is typically defined using a predicate `P : A → Prop`, which assigns a proposition to each element of `A`. The corresponding subtype, denoted as `Subtype P` or `{a : A // P a}`, consists of all elements `a : A` that satisfy `P`.

Subtypes play a crucial role in formal verification, as they allow us to encode mathematical objects with additional properties. 

```lean
structure Subtype.{u} {α : Sort u} (p : α → Prop) : Sort (max 1 u)
number of parameters: 2
fields:
  Subtype.val : α
  Subtype.property : p self.val
constructor:
  Subtype.mk.{u} {α : Sort u} {p : α → Prop} (val : α) (property : p val) : Subtype p
```
We can see that `Subtype` structure in Lean 4 is parameterized by a type `α` and a predicate `p : α → Prop`, which defines adscription to the subtype ` Sort (max 1 u`(or essentially a new type). It includes a constructor, `Subtype.mk`, that takes a value `val : α` and a proof `p val`, which means the value does satisfy `p`, and then produces a subtype `Subtype p` relied on `p`.

### Examples of subtypes

We can define the image of a fucntion by subtype. 

Given two types `A` and `B`, and a function `f : A → B`, we define the image of `f`, denoted as `Im f`, as the subtype of `B` consisting of all elements that are mapped from some `a : A` under `f`.

```lean
def Im {A B : Type} (f : A → B) : Type := { b : B // ∃ (a : A), f a = b }
#check Im
-- Im {A B : Type} (f : A → B) : Type
```

### Elements of a subtype

To create an element of `Subtype P`, we use the `Subtype.mk` function, which maps an element `a : A` and a proof `h : P a` to an element of type `Subtype P`.
```lean
variable (a : A)
variable (P : A → Prop)(h : P a)
#check Subtype.mk a h
-- ⟨a, h⟩ : Subtype P
```
so that we construct a term of `Subtype P`, which is `Subtype.mk a h`(or we can use the syntax candy to denote by `⟨a, h⟩`). 

To define the equality of elements in a subtype, Lean 4 provides two built-in theorems: `Subtype.eq` and `Subtype.eq_iff`
```lean
#print Subtype.eq
-- Subtype.eq.{u} {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }} : a1.val = a2.val → a1 = a2
```
where `.val` is the prime value of the terms in a subtype(you may analog it as preimages). That means once the prime value of `a2` and `a2` are equal, they are considered equal in the subtype.

Conversely, we obviously have `a1 = a2 → a1.val = a2.val`. 
```lean
#print Subtype.eq_iff
-- Subtype.eq_iff.{u_1} {α : Sort u_1} {p : α → Prop} {a1 a2 : { x // p x }} : a1 = a2 ↔ a1.val = a2.val
```
which states that `a1 = a2 ↔ a1.val = a2.val`. 

Within proofs, we can use `rw [Subtype.eq_iff]`/`rw [Subtype.eq]`, `apply Subtype.eq_iff`/`apply Subtype.eq` to rewite the goal or established hypothesis, or `exact Subtype.eq (a = c)` to finish a proof.

### The Inclusion Function

The **inclusion** function is a function of a subtype into its underlying type: it simply extracts the prime value of a `Subtype P` element, discarding its proof.
```lean
def inc {A : Type} {P : A → Prop} : Subtype P → A := by
  intro a
  exact a.val
```
You can analog it as the inverse map.

The inclusion function `inc` is injective.


## Functions and Subtypes

### Restriction

We can formalize the notion of restricting funtions to subtypes. Any function `f : A → B` can be restricted to a subtype by applying `f` only to the underlying values of the subtype elements(or a subset of `A` that satisfy a certain property).

Restriction provides a way to transform elements of type `A → B` into elements of type `Subtype P → B`.

For instance:
```lean
def rest {A B : Type} {P : A → Prop} (f : A → B) : Subtype P → B := by
  intro a
  exact f a.val
```
Here, we restrict the input of `f` by extracting the prime value of `a.val` in the subtype.

### Correstriction

We can also restrict the outputs of functions. Given a function `f : A → B` and a predicate `Q` on `B`, we can correstrict `f` to `Subtype P`, provided that every `b : Im f` satisfies `Q`. If the above condition holds, correstriction provides a way to transform elements of type `A → B` into elements of type `A → Subtype Q`.
```lean
def correct {A B : Type} {Q : B → Prop} (f : A → B)(h : ∀ (b : Im f), Q b.val) : A → Subtype Q := by
  intro a
  have ha : ∃ (a1 : A), f a1 = f a := by
    apply Exists.intro a
    exact rfl
  apply Subtype.mk (f a) (h (Subtype.mk (f a) ha))
```
`have ha : ∃ (a1 : A), f a1 = f a := by` is to prove that `f a` is in `Im f`, by using `a = a1` itself.

### Birrestriction

It is the combination of restriction and correstriction. Given a function `f : A → B`, a predicate `P` on `A` and a predicate `Q` on `B`, we can birrestrict `f` to the respective subtypes, provided that `f a` satisfies `Q` for every `a : Subtype P`. If the above condition holds, birrestriction provides a way to transform elements of type `A → B` into elements of type `Subtype P → Subtype Q`.
```lean
def birrest {A B : Type} {P : A → Prop} {Q : B → Prop} (f : A → B) (h : ∀ (a : A), P a → Q (f a)) : Subtype P → Subtype Q := by
  apply correct (rest f)
  intro ⟨ b, ⟨ a, ha ⟩ ⟩
  simp
  specialize h a.val
  have hb : f a.val = b := ha
  rw [hb] at h
  exact h a.property  
```
where `a.property` is to give a proof of `a` under the predicate(`p a`), or in other word the element in the subtype.

## Equalizers

Given two functions `f g : A → B`, the equalizer of `f` and `g` is the subtype of `A` consisting on all elements `a : A` such that `f a = g a`.
```lean
def Eq {A B : Type} (f g : A → B) : Type := {a : A // f a = g a}
```
We may analog it as a subset of $A$ of all $a$ such that $f(a) = g(a)$.

We can defien the inclusion function of the equalizer:
```lean
def incEq {A B : Type} (f g : A → B) : Eq f g → A := @inc A (fun a => f a = g a)
```
which is a function receiving an element in the equalizer of `f` and `g`, and then returns an element `a` in `A` such that `f a = g a`, which is achieved by `inc`.

This inclusion satisfies that `f ∘ (incEq f g) = g ∘ (incEq f g)`.
```lean
theorem TEqInc {A B : Type} (f g : A → B) : f ∘ (incEq f g) = g ∘ (incEq f g) := by
  apply funext
  intro a
  calc
    (f ∘ (incEq f g)) a = f a.val := rfl
    _ = g a.val := a.property
    _ = (g ∘ (incEq f g)) a := rfl
```

### Universal Property of the equalizer

The universal property states that the pair `(Eq f g, incEq f g)` is initial among all pairs `(C, h)` where `C` is a type and `h : C → A` is a functio satisfying `f ∘ h = g ∘ h`. 

That is if `C` is a type and `h : C → A` is a functio satisfying `f ∘ h = g ∘ h`, then there exists a unique function `u : C → (Eq f g)` such that `(incEq f g) ∘ u = h`. 

The existence of `u`:
```lean
def u {A B C : Type} {f g : A → B} {h : C → A} (h1 : f ∘ h = g ∘ h) : C → Eq f g := by
  intro c
  exact Subtype.mk (h c) (congrFun h1 c)
```

Commutativity `incEq f g ∘ u = h`:
```lean
theorem TEqIncEq {A B C : Type} {f g : A → B} {h : C → A} (h1 : f ∘ h = g ∘ h) : (incEq f g) ∘ (u h1) = h := by
  apply funext
  intro c
  exact rfl
```

Uniqueness of `u`
```lean
theorem TEqUni {A B C : Type} {f g : A → B} {h : C → A} (h1 : f ∘ h = g ∘ h) (v : C → Eq f g) (h2 : ( incEq f g ) ∘ v = h) : v = u h1 := by
  apply funext
  intro c
  apply Subtype.eq
  calc
    (v c).val = ((incEq f g) ∘ v) c := rfl
    _ = h c := congrFun h2 c
    _ = (u h1 c).val := rfl
```