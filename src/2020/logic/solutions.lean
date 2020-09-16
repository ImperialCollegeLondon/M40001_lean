/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import tactic

/-!
# Logic

A Lean companion to the "Logic" part of the intro module.

We develop the basic theory of the five symbols
→, ¬, ∧, ↔, ∨

(in that order)

# Background

It is hard to ask you difficult questions
about the basic theory of these logical operators,
because every question can be proved by "check all the cases".

However, there is this cool theorem, that says that if
a theorem in the basic theory of logical propositions can be proved
by "check all the cases", then it can be proved in the Lean theorem
prover using only the eight constructive tactics `intro`, `apply`,
`assumption`, `exfalso`, `split`, `cases`, `have`, `left` and `right`,
as well as one extra rule called the Law of the Excluded Middle,
which in Lean is the tactic `by_cases`. Note that the tactic `finish`
is a general "check all the cases" tactic, and it uses `by_cases`.

## Reference

* The first half of section 1 of the M40001/40009 course notes.

-/

namespace xena

variables (P Q R : Prop)

/- 

### implies

Some basic practice of `intro`, `apply` and `exact`
-/

/-- Every proposition implies itself. -/
def id : P → P :=
begin
  -- assume P is true. Call this hypotbesis hP.
  intro hP,
  -- then we know that P is true by hypothesis hP.
  exact hP,
end

-- implication isn't associative!
-- Try it when P, Q, R are all false.
example : (false → (false → false)) ↔ true := by simp
example : ((false → false) → false) ↔ false := by simp

-- in Lean, `P → Q → R` is _defined_ to be `P → (Q → R)`
-- Here's a proof of what I just said.
example : (P → Q → R) ↔ (P → (Q → R)) :=
begin
  -- ⊢ P → Q → R ↔ P → Q → R
  refl
end

example : P → Q → P :=
begin
  -- remember that by definition the goal is P → (Q → P),
  -- so it's P implies something, so let's assume 
  -- that P is true and call this hypothesis hP.
  intro hP,
  -- Now we have to prove that Q implies P, so let's
  -- assume that Q is true, and let's call this hypothesis hQ
  intro hQ,
  -- We now have to prove that P is true.
  -- But this is exactly our hypothesis hP.
  exact hP,
end

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`. -/
lemma modus_ponens : P → (P → Q) → Q :=
begin
  -- remember this means "P implies that ((P implies Q) implies Q)"
  -- so let's assume P is true
  intro hP,
  -- and let's assume hypothesis hPQ, that P implies Q
  intro hPQ,
  -- now `hPQ` says `P → Q` and we're trying to prove `Q`!
  -- So by applying the hypothesis `hPQ`, we can reduce
  -- this puzzle to proving `P`.
  apply hPQ,
  -- Now we have to prove `P`. But this is just an assumption
  exact hP, -- or `assumption`
end

lemma trans : (P → Q) → (Q → R) → (P → R) :=
begin
  intros hPQ hQR hP,
  apply hQR,
  apply hPQ,
  exact hP
end

-- This one is a "relative modus ponens" -- in the
-- presence of P, if Q -> R and Q then R.
example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  -- Let `hPQR` be the hypothesis that `P → Q → R`. 
  intro hPQR,
  -- We now need to prove that `(P → Q)` implies something.
  -- So let `hPQ` be hypothesis that `P → Q`
  intro hPQ,
  -- We now need to prove that `P` implies something, so 
  -- let `hP` be the hypothesis that `P` is true.
  intro hP,
  -- We now have to prove `R`.
  -- We know the hypothesis `hPQR : P → (Q → R)`.
  apply hPQR,
    -- we now have two goals, so I indent for a second
    -- The first goal is just to prove P, and this is an assumption
    exact hP,
  -- The number of goals is just one again.
  -- the remaining goal is to prove `Q`. 
  -- But recall that `hPQ` is the hypothesis that `P` implies `Q`
  -- so by applying it,
  apply hPQ,
  -- we change our goal to proving `P`. And this is a hypothesis
  exact hP,
end

/-

### not

`not P`, with notation `¬ P`, is defined to mean `P → false` in Lean,
i.e., the proposition that P implies false. You can easily check with
a truth table that P → false and ¬ P are equivalent, but we need to 
remember the fact that in Lean ¬ P was *defined* to mean `P → false`
and not any other way

We develop a basic interface.
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

theorem not_not_intro'' : P → ¬ (¬ P) :=
begin
  apply modus_ponens,
end

-- lambda calculus proof
theorem not_not_intro' : P → ¬ (¬ P) :=
λ hP hnP, hnP hP

theorem contra : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro hPQ,
  intro hnQ,
  intro hP, -- we take the assumptions in a some order
  apply hnQ,
  apply hPQ,
  exact hP, -- and then we put them back in a different order
end

/-!

### and

The hypothesis `hPaQ : P ∧ Q` in Lean, is equivalent to
hypotheses `hP : P` and `hQ : Q`. 

If you have `hPaQ` as a hypothesis, and you want to get to
`hP` and `hQ`, you can use the `cases` tactic.

If you have `⊢ P ∧ Q` as a goal, and want to turn the goal
into two goals `⊢ P` and `⊢ Q`, then use the `split` tactic.

Note that after `split` it's good etiquette to use braces
e.g.

example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
  { exact hP },
  { exact hQ }
end

but for this sort of stuff I think principled indentation
is OK

```
example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
    exact hP,
  exact hQ
end
```

-/

theorem and.elim_left : P ∧ Q → P :=
begin
  intro hPaQ,
  cases hPaQ with hP hQ,
  exact hP,
end

theorem and.elim_right : P ∧ Q → Q := λ hPaQ, hPaQ.2

theorem and.intro : P → Q → P ∧ Q :=
begin
  intro hP,
  intro hQ,
  split; assumption
end

-- the "eliminator for and" -- if you know `P ∧ Q` you
-- can deduce that something implies something else
-- with no ands
theorem and.elim : P ∧ Q → (P → Q → R) → R :=
begin
  intro hPaQ,
  cases hPaQ with hP hQ,
  intro hPQR,
  apply hPQR; assumption
end

theorem and.rec : (P → Q → R) → P ∧ Q → R :=
begin
  intro hPQR,
  rintro ⟨hP, hQ⟩,
  apply hPQR; assumption
end

-- joke proof
theorem and.elim' : P ∧ Q → (P → Q → R) → R :=
begin
  intro hPaQ,
  intro hPQR,
  apply and.rec, -- anarchy
    exact hPQR,
  exact hPaQ,
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

theorem and.trans : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  rintro ⟨hP, hQ⟩,
  rintro ⟨hQ2, hR⟩,
  split; assumption
end

/-
Extra credit

Recall that the convention for the implies sign →
is that it is _right associative_, by which
I mean that `P → Q → R` means `P → (Q → R)` by definition.
This does actually simplify! If `P` implies `Q → R`
then this means that `P` and `Q` together, imply `R`,
so `P → Q → R` is logically equivalent to `(P ∧ Q) → R`.

We proved that `P → Q → R` implied `(P ∧ Q) → R`; this was `and.rec`.
Let's go the other way.
-/

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intro hPaQR,
  intro hP, 
  intro hQ,
  apply hPaQR,
  split; assumption
end


/-!

### iff

The basic theory of `iff`.

In Lean, `P ↔ Q` is *defined to mean* `(P → Q) ∧ (Q → P)`.

It is _not_ defined by a truth table.

This changes the way we think about things.
-/

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

-- refl tactic also works
def iff.refl'' : P ↔ P :=
begin
  refl
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

def iff.symm' : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  -- introduction of the rewrite tactic
  rw h,
  -- refl automatically applied
end

-- Instead of begin/end blocks, which many mathematicians prefer,
-- one can write proofs in the lambda calculus, with some
-- computer scientists like better

def iff.symm'' : (P ↔ Q) → (Q ↔ P) :=
λ ⟨hPQ, hQP⟩, ⟨hQP, hPQ⟩

-- That's a full proof.

def iff.comm : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split;
  apply iff.symm,
end

-- without rw or cc this is ugly
def iff.trans :  (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  rintro ⟨hPQ, hQP⟩,
  rintro ⟨hQR, hRQ⟩,
  split, -- split; cc finishes it
    intro hP,
    apply hQR,
    apply hPQ,
    exact hP,
  intro hR,
  apply hQP,
  apply hRQ,
  exact hR,
end

def iff.trans' :  (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro hPiQ,
  intro hQiR,
  rw hPiQ,
  assumption
end

def iff.boss : ¬ (P ↔ ¬ P) :=
begin
  rintro ⟨h1, h2⟩,
  have hnp : ¬ P,
    intro hP,
    apply h1; assumption,
  apply hnp,
  apply h2,
  exact hnp,


end

-- Now we have iff we can go back to and.

/-! ### ↔ and ∧ -/

theorem and_comm : P ∧ Q ↔ Q ∧ P :=
begin
  split,
    apply and.symm,
  apply and.symm
end

theorem and_comm' : P ∧ Q ↔ Q ∧ P :=
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



/-!

## Or

`P ∨ Q` is true when at least one of `P` and `Q` are true.
Here is how to work with `∨` in Lean.

If you have a hypothesis `hPoQ : P ∨ Q` then you 
can break into the two cases `hP : P` and `hQ : Q` using
`cases hPoQ with hP hQ`

If you have a _goal_ of the form `⊢ P ∨ Q` then you
need to decide whether you're going to prove `P` or `Q`.
If you want to prove `P` then use the `left` tactic,
and if you want to prove `Q` then use the `right` tactic.

-/

-- recall that P, Q, R are Propositions. We'll need S for this one.
variable (S : Prop)

-- use the `left` tactic to reduce from `⊢ P ∨ Q` to `⊢ P`
theorem or.intro_left : P → P ∨ Q :=
begin
  intro hP,
  -- ⊢ P ∨ Q
  left,
  -- ⊢ P
  exact hP
end

-- use the `right` tactic to reduce from `⊢ P ∨ Q`
theorem or.intro_right : Q → P ∨ Q :=
begin
  sorry,
end

theorem or.elim : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intro h,
  intros hpq hqr,
  cases h,
  sorry, sorry
end


theorem or.symm : P ∨ Q → Q ∨ P :=
begin
  intro hPoQ,
  cases hPoQ with hP hQ,
    right, 
    assumption,
  left,
  assumption
end

theorem or.comm : P ∨ Q ↔ Q ∨ P :=
begin
  split,
    apply or.symm,
  apply or.symm
end

-- good luck!

theorem or.assoc : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
begin
  split,
    rintro (⟨hP | hQ⟩ | hR),
    { left, assumption},
    { right, left, assumption},
    { right, right, assumption},
    -- don't get lost. Hover over `rintro` to see the docs.
  rintro (hP | hQ | hR),
    { left, left, assumption},
    { left, right, assumption},
    { right, assumption},  
end

theorem or.cases_on : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  rintro (hP | hQ),
  cc,cc,
end



theorem or.imp : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  rintros hPR hQS (hP | hQ),
    left, cc,
  right, cc
end

theorem or.imp_left : (P → Q) → P ∨ R → Q ∨ R :=
begin
  rintros hPQ (hP | hR),
    left, cc,
    right, assumption
end

theorem or.imp_right : (P → Q) → R ∨ P → R ∨ Q :=
begin
  rintros hPQ (hP | hR),
    left, cc,
    right, cc,
end

theorem or.left_comm : P ∨ Q ∨ R ↔ Q ∨ P ∨ R :=
begin
  rw or.comm,
  rw or.assoc,
  rw or.comm R,
  -- (refl)
end

theorem or.rec : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  rintros _ _ (_ | _);
  cc
end

theorem or.resolve_left : P ∨ Q → ¬P → Q :=
begin
  rintros (hP | hQ) hnP,
    contradiction,
  assumption
end

theorem or_congr : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  rintros hPR hQS,
  rw hPR,
  rw hQS,
end

theorem or_false : P ∨ false ↔ P :=
begin
  simp,
end


/-!

# Classical logic

-/

-- useful lemma about false
theorem false.elim' : false → P :=
begin
  -- Let's assume that a false proposition is true. Let's
  -- call this assumption h.
  intro h,
  -- We now have to prove P. 
  -- The `exfalso` tactic changes any goal to `false`.
  exfalso,
  -- Now our goal is an assumption! It's exactly `h`.
  exact h,
end

-- This one cannot be proved using the tactics we know
-- which are constructive. This one needs the assumption
-- that every LEM blah 
theorem double_negation_elimination : ¬ (¬ P) → P :=
begin
  -- `tauto!` works
  classical,
  by_cases hP : P,
    intro h37,
    assumption,
  intro hnnP,
  exfalso,
  apply hnnP,
  exact hP,
end


end xena
