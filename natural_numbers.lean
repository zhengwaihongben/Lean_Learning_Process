/-
A Lean 4 document for Chapter 6 Natural Numbers
-/

-- Define N which is isomorphic to Nat
inductive N : Type where
  | Z : N
  | S : N → N
deriving Repr

-- Injection
def injective {A B : Type} (f : A → B) : Prop := ∀{a1 a2 : A}, (f a1 = f a2) → (a1 = a2)
-- Surjection
def surjective {A B : Type}(f : A → B): Prop := ∀ (y : B), ∃ (x : A), f x = y

open N

/-
Define the basic operations over N
-/

-- max(n, m)
def max : N → N → N := by
  intro n m
  match n, m with
  | Z, m => exact m
  | n, Z => exact n
  | S n, S m => exact S (max n m)

-- min(n, m)
def min : N → N → N := by
  intro n m
  match n, m with
  | Z, _ => exact Z
  | _, Z => exact Z
  | S n, S m => exact S (min n m)

-- n + m
def Addition : N → N → N := by
  intro n m
  cases n with
  | Z => exact m
  | S n => exact S (Addition n m)

-- n * m
def Multiplication : N → N → N := by
  intro n m
  cases n with
  | Z => exact Z    -- If n = Z, then Z * m = Z
  | S n => exact Addition (Multiplication n m) m

-- Assigning notation to the addition and multiplication
notation : 65 lhs:65 " + " rhs:66 => Addition lhs rhs
notation : 70 lhs:70 " * " rhs:71 => Multiplication lhs rhs

-- Denote 'one' as the successor of 'Z'
def one : N := S Z


/-
Some basic properties of operations on Natural Numbers
-/

-- Symmetry of Natural Numbers
theorem symmetry : ∀ {a b : N}, a = b ↔ b = a := by
  intro a b
  constructor
  . intro h
    exact h.symm
  . intro p
    exact p.symm

-- Transitiviy of Natural Numbers
theorem transitivity {a b c: N} (h1 : a = b)(h2 : b = c) : a = c := by
  calc
    a = b := by exact h1
    _ = c := by exact h2

-- Z is the identity element of addition
-- 1. Z is the left identity element of addition
theorem Nat0LeftIdenAdd : ∀ {n : N}, n + Z = n := by
  intro n
  induction n
  -- case Z
  rfl
  -- case S
  rename_i n h
  calc
    n.S + Z = (n + Z).S := by rfl
    _ = n.S := by rw [h]
-- 2. Z is the right identity element of addition
theorem Nat0RightIdenAdd : ∀ {n : N}, Z + n = n := by
  intro n
  induction n
  -- case Z
  rw [Nat0LeftIdenAdd]  -- or directly rfl by definition
  -- case S
  rename_i n h
  rfl  -- by definition of addition

-- Associativity
theorem add_succ (n m : N) : n + m.S = (n + m).S := by
  induction n
  rfl
  rename_i n h
  calc
    n.S + m.S = (n + m.S).S := by rfl
    _ = ((n + m).S).S := by rw [h]

-- Commutativity
theorem NatCommuInAdd : ∀ {m n : N}, m + n = n + m := by
  intro m n
  induction m
  -- case Z
  calc
    Z + n = n :=by exact Nat0RightIdenAdd
    _ = n + Z :=by rw [Nat0LeftIdenAdd]
  -- case S
  rename_i m ih
  calc
    m.S + n = (m+n).S := by rfl
    _ = (n+m).S := by rw[ih]
    _ = n + m.S := by rw[add_succ]

-- Associativity
theorem NatAddAssoc (a b c : N) : (a + b) + c = a + (b + c) := by
  induction a
  rfl
  rename_i a h
  calc
    a.S + b + c = (a + b).S + c := by rfl
    _ = (a + b + c).S := by rfl
    _ = (a + (b + c)).S := by rw [h]

-- Law of Left Distribution
theorem LeftDist (a b c : N) : a * ( b + c ) = a*b + a*c := by
  induction a
  -- case Z
  rfl
  -- case S
  rename_i a h
  calc
    a.S * (b + c) = a * (b + c) + (b + c) := by rfl
    _ = a * b + a * c + (b + c) := by rw [h]
    _ = a * b + (a * c + (b + c)) := by rw [NatAddAssoc]
    _ = a * b + ((a * c + b) + c) := by rw [NatAddAssoc]
    _ = a * b + ((b + a * c) + c) := by rw [NatCommuInAdd (m := a * c) (n := b)]
    _ = a * b + (b + (a * c + c)) := by rw [NatAddAssoc]
    _ = (a * b + b) + (a * c + c) := by rw [← NatAddAssoc]
    _ = a.S * b + a.S * c := by rfl

/-
Define the order of N
-/
inductive Lt : N → N → Prop
  | zero_lt (n : N) : Lt Z n.S  -- 0 is less than any nonzero natural numbers
  | succ_lt {a b : N} : Lt a b → Lt a.S b.S  -- If a < b, then a.S < b.S
instance : LT N := { lt := Lt }
/-
Lt is a built-in type class, which allows the symbol '<' to be assigned:
class LT (α : Type u) where
  lt : α → α → Prop
-/

-- n < n.S
theorem Lt_succ (n : N) : n < n.S := by
  induction n
  -- case Z
  exact Lt.zero_lt Z
  -- case S
  rename_i n h
  exact Lt.succ_lt h

-- 0 is the least element in N
theorem zeroleast (n : N)(h : n ≠ Z) : Z < n := by
  cases n with
  | Z => contradiction
  | S =>
    rename_i n
    exact Lt.zero_lt n

-- Anti-reflexibility
theorem antireflexibiliy (n : N) : ¬ n < n := by
  intro h
  induction n
  -- case Z
  contradiction
  -- S
  rename_i n p
  cases h
  rename_i q
  exact p q

-- Transitivity
theorem transitv {a b c : N}(hab : a < b)(hbc : b < c) : a < c := by
-- since '<' is an inductive type, we can do the induction to b < c
  induction hbc generalizing a with
  | zero_lt n =>
  /-
  In this case
  b = Z
  c = S n
  hbc = Lt.zero_lt_succ n
  -/
      contradiction
  | @succ_lt b' c' hbc' ih =>  -- @ is to extract the implicit parameters as {a b : N} are implicit in succ_lt_succ
      cases hab with
      | zero_lt _ => exact Lt.zero_lt c'
      | succ_lt hab' => exact Lt.succ_lt (ih hab')

-- N is Well-ordered


-- Divisibility of N

