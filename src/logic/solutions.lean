/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
theorem dne (P : Prop) : ¬ (¬ P) → P :=
begin
  tautology
end

import tactic

/-!
# Logic

We develop the basic theory of the five symbols
∧, ∨, ¬, → and ↔ in Lean

# Background

It is impossible to ask you difficult questions
about the basic theory of these logical operators,
because every question can be proved by "check all the cases".

However, there is this cool theorem, that says that if
a theorem in the basic theory of logical propositions can be proved
by "check all the cases", then it can be proved in the Lean theorem
prover using only the tactics `intro`, `apply`, `exact`, `split`,
`cases`, `have`, `left` and `right`, as well as one extra rule called
the Law of the excluded middle, which in Lean is the tactic `by_cases`.
Note that the tactic `tauto!` is a general "check all the cases"
tactic, and it uses `by_cases`.

## Reference
* The first half of section 1 of the M40001/40009 course notes.

-/

namespace xena

variables (P Q R : Prop)

/-

### false

`false` is defined to be the type with no terms. If you see a term
of type `false` then you can do `cases` on it, and it will split
into all possible cases. Because there aren't any cases, your
goal will be automatically proved.
-/

theorem false.elim : false → P :=
begin
  intro h,
  cases h, -- no cases
end

/-
### not

`not P`, with notation `¬ P`, is *defined* to mean `P → false`.

-/

theorem not_not_intro : P → ¬ (¬ P) :=
begin
  -- we have to prove that P implies (not (not P)),
  -- so let's assume P is true, and let's call this assumption hP
  intro hP,
  -- now we have to prove `not (not P)`, a.k.a. `¬ (¬ P)`, and
  -- by definition this means we have to prove `(¬ P) → false`
  -- So let's let hnP be the hypothesis that `¬ P` is true.
  intro hnP,
  -- and now we have to prove `false`!
  -- Sometimes this can be difficult, but it's OK if you have
  -- *contradictory hypotheses*, because with contradictory
  -- assumptions you can prove false conclusions, and once you've
  -- proved one false thing you've proved all false things because
  -- you've made mathematics collapse.

  -- How are we going to use hypothesis `hnP : ¬ P`? 

  -- Well, what does it _mean_? It means `P → false`,
  -- and our _goal_ is false, so why don't we apply 
  -- hypothesis hnP, which will reduce our problem
  -- to proving `P`.

  apply hnP,

  -- now our goal is `P`, and this is an assumption!
  exact hP
end

-- lambda calculus proof
theorem not_not_intro' : P → ¬ (¬ P) :=
λ hP hnP, hnP hP

open classical

open_locale classical

theorem double_negation_elimination : ¬ (¬ P) → P :=
begin
  tautology !,
  -- have to do it by cases on P being true or calse
  by_cases hP : P,
    tauto,
    tauto,

end


#check dne
example [decidable P] : ¬ (¬ P) → P := by library_search

/-!
### iff

The basic theory of `iff`.

In Lean, `P ↔ Q` is *defined to mean* `(P → Q) ∧ (Q → P)`.

It is _not_ defined by a truth table.

This changes the way we think about things.
-/

/-- Every proposition implies itself. -/
def id : P → P :=
begin
  -- assume P is true. Call this hypotbesis hP.
  intro hP,
  -- then we know that P is true by hypothesis hP.
  exact hP,
end

/-- `P ↔ P` is true for all propositions `P`. -/
def iff.refl : P ↔ P :=
begin
  -- By Lean's definition I need to prove (P → P) ∧ (P → P)
  split,
  { -- need to prove P → P
    apply id },
  { -- need to prove P → P
    apply id }
end

-- If you get stuck, there is always the "truth table" tactic `tauto!`
def iff.refl' : P ↔ P :=
begin
  tauto!, -- the "truth table" tactic.
end

def iff.symm : (P ↔ Q) → (Q ↔ P) :=
begin
  -- assume P ↔ Q is true. Call this hypothesis hPiQ.
  intro hPiQ,
  -- by definition, hPiQ means that P → Q is true and Q → P is true.
  -- Let's call these assumptions hPQ and hQP.
  cases hPiQ with hPQ hQP,
  --  We want to prove Q ↔ P
  -- but by definition this just means (Q → P) ∧ (P → Q)
  -- We split this goal, and then both goals are assumptions
  -- (one is hPQ, one is hQP)
  split; assumption,
end

-- Instead of begin/end blocks, which many mathematicians prefer,
-- one can write proofs in the lambda calculus, with some
-- computer scientists like better

def iff.symm' : (P ↔ Q) → (Q ↔ P) :=
λ ⟨hPQ, hQP⟩, ⟨hQP, hPQ⟩

-- That's a full proof.

def iff.comm : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split;
  apply iff.symm,
end

/-
Here's a funny thing.

What should Lean do when it sees
the maths formula a-b-c? Should it interpret it
as meaning (a-b)-c or a-(b-c)?
Human convention is (a-b)-c.
But what should Lean do


def iff.trans :  (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin

end


theorem and.symm : P ∧ Q → Q ∧ P :=
begin
  -- goal is `⊢ P ∧ Q → Q ∧ P`
    intro h, -- `h : P ∧ Q`
    cases h with hP hQ, -- `hP : P` and `hQ : Q` 
    split, -- two goals now, `⊢ Q` and `⊢ P`
    { exact hQ },
    { exact hP }, 
end

-- term mode proof
theorem and.symm' : P ∧ Q → Q ∧ P :=
λ ⟨P, Q⟩, ⟨Q, P⟩


theorem and_comm : P ∧ Q ↔ Q ∧ P :=
⟨and.symm _ _, and.symm _ _⟩


-- ∧ is "right associative" in Lean, which means
-- that `P ∧ Q ∧ R` is _defined to mean_ `P ∧ (Q ∧ R)`.
-- Associativity can hence be written like this:
theorem and_assoc : ((P ∧ Q) ∧ R) ↔ (P ∧ Q ∧ R) :=
begin
  split,
  { rintros ⟨⟨hP, hQ⟩, hR⟩,
    exact ⟨hP, hQ, hR⟩ },
  { rintros ⟨hP, hQ, hR⟩,
    exact ⟨⟨hP, hQ⟩, hR⟩ },  
end

#check or.symm
theorem or_comm : P ∨ Q ↔ Q ∨ P :=
begin
  
end

end xena
