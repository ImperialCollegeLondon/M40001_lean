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

## Level 1 : implies

In Lean, `P → Q` is the notation for `P ⇒ Q` . 

Let's start by learning how to control implications. We will
learn the three tactics `intro`, `apply` and `exact`.

-/

/-- Every proposition implies itself. -/
def id : P → P :=
begin
  /- 
  Click here!
  
  See that
  
  `⊢ P → P`

  on the top right? That funny symbol `⊢ X` means "you have to prove `X`".

  So we have to prove that `P` implies `P`.

  How do we prove that `X` implies `Y`? We assume `X`, and try and deduce `Y`.
  -/
  -- assume P is true. Call this hypothesis hP.
  intro hP,
  -- goal now `⊢ P` and we also have hypothesis `hP: P`
  -- So we know that P is true, by hypothesis hP.
  exact hP,
end

-- implication isn't associative!
-- Try it when P, Q, R are all false.
-- `false → (false → false)` is `true`,
-- and
-- `(false → false) → false` is `false`.

-- in Lean, `P → Q → R` is _defined_ to be `P → (Q → R)`
-- Here's a proof of what I just said.
example : (P → Q → R) ↔ (P → (Q → R)) :=
begin
  -- ⊢ P → Q → R ↔ P → Q → R
  refl -- that closes goals of the form X = X and X ↔ X.
end

-- Another way to see it is just to uncomment out the line below:
-- #check P → (Q → R) -- output is `P → Q → R : Prop`

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

-- See if you can do this one yourself. Replace the `sorry` with a proof.
lemma transitivity : (P → Q) → (Q → R) → (P → R) :=
begin
  sorry,
end

-- Of course you can always cheat with the `finish` tactic
example : (P → Q) → (Q → R) → (P → R) :=
begin
  finish,
end

-- finish just checks all the cases. It's slower than a constructive proof.
-- constructivists regard it as cheating.

-- This one is a "relative modus ponens" -- in the
-- presence of P, if Q -> R and Q then R.
-- Something fun happens in this one. I'll start you off.
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
  -- Can we apply it?
  apply hPQR,
  -- exercise: what just happened?
  sorry, sorry
end

/-

### Level 2 : not

`not P`, with notation `¬ P`, is defined to mean `P → false` in Lean,
i.e., the proposition that P implies false. Note that `true → false` is `false`,
and `false → false` is `true`, so `P → false` is indeed equivalent
to `¬ P`. But we need to remember the fact that in Lean, `¬ P` was
*defined* to mean `P → false` and not in any other way.

We develop a basic interface for `¬`.
-/

theorem not_not_intro : P → ¬ (¬ P) :=
begin
  -- we have to prove that P implies (not (not P)),
  -- so let's assume P is true, and let's call this assumption hP
  intro hP,
  -- now we have to prove `not (not P)`, a.k.a. `¬ (¬ P)`, and
  -- by definition this means we have to prove `(¬ P) → false`
  -- In fact we can `change` our goal to this
  change ¬ P → false,
  -- The `change` tactic will make changes to the goal, as long
  -- as they are true *by definition*.

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
  -- We could `change` `hnP` to remind us of this:
  change P → false at hnP,

  -- Now our _goal_ is false, so why don't we apply 
  -- hypothesis hnP, which will reduce our problem
  -- to proving `P`.

  apply hnP,

  -- now our goal is `P`, and this is an assumption!
  exact hP
end

-- What do you think of this proof?
theorem not_not_intro'' : P → ¬ (¬ P) :=
begin
  apply modus_ponens,
  -- Go back and look at modus ponens. Can you see how this proof worked?
end

-- If you're into lambda calculus or functional programming,
-- here's a functional proof
theorem not_not_intro' : P → ¬ (¬ P) :=
λ hP hnP, hnP hP

-- This one is straightforward -- give it a go:
theorem contra1 : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry
end

-- This way is impossible using constructive logic -- you have to use
-- a classical tactic like `finish` or check manually on cases.
theorem contra2 : (¬ Q → ¬ P) → (P → Q) :=
begin
  intro h,
  intro hP,
  -- stuck
  finish,
end


/-!

### Level 3 : and

The hypothesis `hPaQ : P ∧ Q` in Lean, is equivalent to
hypotheses `hP : P` and `hQ : Q`. 

If you have `hPaQ` as a hypothesis, and you want to get to
`hP` and `hQ`, you can use the `cases` tactic.

If you have `⊢ P ∧ Q` as a goal, and want to turn the goal
into two goals `⊢ P` and `⊢ Q`, then use the `split` tactic.

Note that after `split` it's good etiquette to use indentation
or brackets, because you have two goals.

Example:

example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
    exact hP, -- we had two goals here
  exact hQ  -- we are back to one goal
end

or

example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
  { exact hP },
  { exact hQ }
end

-/

theorem and.elim_left : P ∧ Q → P :=
begin
  intro hPaQ,
  -- You can use the `cases` tactic on an `and` hypothesis
  cases hPaQ with hP hQ,
  exact hP,
end

-- try this one
theorem and.elim_right : P ∧ Q → Q :=
begin
  sorry
end

-- functional proof
theorem and.elim_right' : P ∧ Q → Q := λ hPaQ, hPaQ.2

-- Can you construct the full eliminator for `and`?
theorem and.elim : P ∧ Q → (P → Q → R) → R :=
begin
  sorry
end

-- Here's how to solve `and` goals.
theorem and.intro : P → Q → P ∧ Q :=
begin
  intro hP,
  intro hQ,
  -- use `split` on an and goal; you'll get two goals.
  split,
    assumption, -- just means "the goal is one of the hypotheses"
  assumption,
end


-- there's a two-line proof of this which starts
-- `apply function.swap`, but you don't need to do this
theorem and.rec : (P → Q → R) → P ∧ Q → R :=
begin
  sorry
end

theorem and.symm : P ∧ Q → Q ∧ P :=
begin
  sorry
end

theorem and.trans : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  sorry,
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
  sorry
end


/-!

### Level 4 : iff

The basic theory of `iff`.

In Lean, `P ↔ Q` is *defined to mean* `(P → Q) ∧ (Q → P)`.

It is _not_ defined by a truth table. You can attack a `P ↔ Q` goal
with the `split` tactic, because it is really an `∧` statement.
-/

/-- `P ↔ P` is true for all propositions `P`. -/
def iff.refl : P ↔ P :=
begin
  -- By Lean's definition I need to prove (P → P) ∧ (P → P)
  split,
    -- need to prove P → P
    -- We proved that a long time ago and called it `id`.
    apply id,
  -- need to prove P → P
  apply id
end

-- If you get stuck, there is always the "truth table" tactic `finish`
def iff.refl' : P ↔ P :=
begin
  finish,
end

-- The refl tactic also works
def iff.refl'' : P ↔ P :=
begin
  refl
end


def iff.symm : (P ↔ Q) → (Q ↔ P) :=
begin
  -- Try this one using `cases` and `split`.
  sorry
end

-- I'll now show you a better way: the `rewrite` tactic.
def iff.symm' : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  -- `h : P ↔ Q`
  -- The `rw h` tactic will change all P's in the goal to Q's.
  -- And then it will try `refl`, just for luck
  rw h,
  -- finished! Goal becamse `Q ↔ Q` and then `refl` finished it.
end

def iff.comm : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  sorry,
end

-- without rw or cc this is ugly
def iff.trans :  (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  sorry
end

-- This is a cute question. Can you prove it constructively,
-- using only `intro`, `cases`, `have`, `apply`, and `assumption`?
def iff.boss : ¬ (P ↔ ¬ P) :=
begin
  sorry
end

-- Now we have iff we can go back to and.

/-! ### iff epilogue: ↔ and ∧ -/

theorem and.comm : P ∧ Q ↔ Q ∧ P :=
begin
  sorry
end

-- ∧ is "right associative" in Lean, which means
-- that `P ∧ Q ∧ R` is _defined to mean_ `P ∧ (Q ∧ R)`.
-- Associativity can hence be written like this:
theorem and_assoc : ((P ∧ Q) ∧ R) ↔ (P ∧ Q ∧ R) :=
begin
  sorry,
end



/-!

## Level 5 (final level) : Or

`P ∨ Q` is true when at least one of `P` and `Q` are true.
Here is how to work with `∨` in Lean.

If you have a _hypothesis_ `hPoQ : P ∨ Q` then you 
can break into the two cases `hP : P` and `hQ : Q` using
`cases hPoQ with hP hQ`

If you have a _goal_ of the form `⊢ P ∨ Q` then you
need to decide whether you're going to prove `P` or `Q`.
If you want to prove `P` then use the `left` tactic,
and if you want to prove `Q` then use the `right` tactic.
Don't get lost! You can't go back.
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
  intro hPoQ,
  intros hpq hqr,
  -- use the `cases h` tactic if `h : X ∨ Y`
  cases hPoQ with hP hQ,
    sorry,
  sorry
end


theorem or.symm : P ∨ Q → Q ∨ P :=
begin
  sorry
end

theorem or.comm : P ∨ Q ↔ Q ∨ P :=
begin
  sorry
end

theorem or.assoc : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
begin
  sorry,
end

theorem or.cases_on : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  sorry,
end



theorem or.imp : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  sorry,
end

theorem or.imp_left : (P → Q) → P ∨ R → Q ∨ R :=
begin
  sorry,
end

theorem or.imp_right : (P → Q) → R ∨ P → R ∨ Q :=
begin
  sorry,
end

theorem or.left_comm : P ∨ Q ∨ R ↔ Q ∨ P ∨ R :=
begin
  sorry,
end

theorem or.rec : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  sorry
end

theorem or.resolve_left : P ∨ Q → ¬P → Q :=
begin
  sorry,
end

theorem or_congr : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  sorry,
end

/-!

# Appendix: `exfalso` and classical logic

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

-- Is that confusing? What about this proof?
theorem false.elim'' : false → P :=
begin
  -- Let's assume that a false proposition is true. Let's
  -- call this assumption h.
  intro h,
  -- Now let's deal with all the cases.
  cases h,
  -- There are no cases.
end

-- This next one cannot be proved using the tactics we know
-- which are constructive. This one needs the assumption
-- that every statement is true or false.
-- We give a "by cases" proof explicitly -- `finish` just does the
-- job immediately.
theorem double_negation_elimination : ¬ (¬ P) → P :=
begin
  -- `finish` works
  classical,
  intro hnnP,
  by_cases hP : P,
    -- hypothesis hP : P
    assumption,
  -- hypothesis hP : ¬ P
  -- `contradiction` works from here
  exfalso,
  apply hnnP,
  exact hP,
end

end xena
