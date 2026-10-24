-- 3.4

section exercise_3_4
variable (A : Type)
variable (a b c : A)
variable (R : Prop)

theorem E1_3_4 : ( ∃ (a : A), R ) → R := by
  intro h
  apply Exists.elim h
  intro a
  intro hr
  exact hr

theorem E2_3_4 (a : A) : R → ( ∃ (a : A), R ) := by
  intro h
  exact Exists.intro a h

theorem E3_3_4 (P : A → Prop) (a : A) (R : Prop) : ( ∃ (a : A), P a ∧ R ) ↔ ( ∃ (a : A), P a ) ∧ R := by
  apply Iff.intro
  intro hl
  cases hl with
  | intro a sta =>
    apply And.intro
    exact Exists.intro a sta.left
    exact sta.right
  intro hr
  have hrl : (∃ a, P a) := hr.left
  cases hrl with
  | intro a stb =>
    have hR : R := hr.right
    exact Exists.intro a (And.intro stb hR)

variable (P Q : A → Prop)
theorem E4_3_4 : ( ∃ (a : A), (P a ∨ Q a) ) ↔ ( ∃ (a : A), P a ) ∨ ( ∃ (a : A), Q a ) := by
  apply Iff.intro
  .
    intro hl
    cases hl with
    | intro a sta =>
      cases sta with
      | inl staL =>
        exact Or.inl (Exists.intro a staL)
      | inr star =>
        exact Or.inr (Exists.intro a star)
  .
    intro hr
    cases hr with
    | inl hrl =>
      cases hrl with
      | intro a sta =>
        exact Exists.intro a (Or.inl sta)
    | inr hrr =>
      cases hrr with
      | intro a sta =>
        exact Exists.intro a (Or.inr sta)

open Classical

theorem E5_3_4 : ( ∀ (a : A), P a ) ↔ ¬( ∃ (a : A), ¬( P a) ) := by
  apply Iff.intro
  .
    intro con
    intro negcon
    cases negcon with
    | intro a negP =>
      specialize con a
      exact negP con  -- ¬P a is a function receive P a and then return False
  .
    intro negP
    intro a
    apply byContradiction
    intro negQ
    exact negP (Exists.intro a negQ)

theorem E6_3_4 : ( ∃ (a : A), P a ) ↔ ¬ ( ∀ (a : A), (¬ P a) ) := by
  apply Iff.intro
  .
    intro h1
    apply Exists.elim h1
    intro a
    intro sta1  -- ¬ ∀ (a : A), ¬P a <=> ∀ (a : A), ¬P a → False
    intro con1
    specialize con1 a
    exact con1 sta1
  .
    intro h2
    apply byContradiction
    intro con1
    apply h2
    intro a
    intro con2
    apply con1
    exact Exists.intro a con2

theorem E7_3_4 : ( ¬ ∃ (a : A), P a ) ↔ ( ∀ (a : A), (¬P a) ) := by
  apply Iff.intro
  .
    intro con1
    intro a
    intro con2
    exact con1 (Exists.intro a con2)
  .
    intro con3
    intro con4
    cases con4 with
    | intro a con5 =>
    specialize con3 a
    exact con3 con5

theorem E11_3_4 (a : A) : ( ∃ (a : A), R → P a ) → (R → ∃ (a : A), P a) := by
  intro h1
  intro b
  cases h1 with
  | intro a h2 =>
  have h3 : P a := by
    apply h2
    exact b
  exact Exists.intro a h3

#print axioms E11_3_4

#print Ne

#check Eq.trans

#print DecidableEq
#print Decidable.isFalse
#check Decidable.isFalse

#check DecidableEq Bool

#print propext

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
