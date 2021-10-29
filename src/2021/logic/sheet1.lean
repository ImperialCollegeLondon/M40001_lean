/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 1 : "implies" (`→`)

We learn about propositions, and implications `P → Q` between them. You can get
this arrow by typing `\to` or `\r`. Mathematicians usually write the
implication arrow as `P ⇒ Q` but Lean prefers a single arrow.

## The absolute basics

`P : Prop` means that `P` is a true-false statement. `h : P` means
that `h` is a proof that `P` is true, or you can regard `h` as an
assumption that `P` is true; logically these are the same. Stuff above
the `⊢` symbol is your assumptions. The statement to the right of it is
the goal. Your job is to prove the goal from the assumptions.

## Tactics you will need

To solve the levels on this sheet you will need to know how to use the
following tactics:

* `intro`
* `exact`
* `apply`

### The `intro` tactic

Mathematical background: `intro h,` says "To prove `P → Q`, you can assume
that `P` is true (call this assumption `h`) and then it
suffices to prove `Q`."

Lean: If your goal is `⊢ P → Q` then `intro h,` will introduce a
hypothesis `h : P` (i.e. a hypothesis that `P` is true)
and change the goal to `⊢ Q`. 

### The `exact` tactic

Mathematics: If you have an assumption `h` that `P` is true,
and your goal is to prove that `P` is true, then `exact h,`
will solve this goal.

Lean: If your goal is `⊢ P` and you have a hypothesis `h : P`
then `exact h,` will solve it.

### The `apply` tactic

Mathematics: `apply` is *arguing backwards*. It is like "it suffices to...".
If you're trying to prove `Q`, and you know `h : P → Q` is true, then it
suffices to prove `P`. So `apply h,` *changes the goal* from `Q` to `P`. The key
point to remember is that `apply h` will only work when `h` is an implication,
and it will only work when the *conclusion* of `h` *matches the goal*.

Lean: If your goal is `⊢ Q` and you have `h : P → Q` then `apply h,` will
change the goal to `⊢ P`.

-/

/-

## Worked examples

Click around in the proofs to see the tactic state (on the right) change.
The tactic is implemented and the state changes just before the comma.
I will use the following conventions: variables with capital
letters like `P`, `Q`, `R` denote propositions
(i.e. true/false statements) and variables whose names begin
with `h` like `h1` or `hP` are proofs or hypotheses.



-/ 

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variables (P Q R : Prop)

-- Here are some examples of `intro`, `exact` and `apply` being used.

-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.
example (hP : P) (hQ : Q) (hR : R) : P :=
begin
  -- note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.
  exact hP,
end

-- Assume `Q` is true. Prove that `P → Q`. 
example (hQ : Q) : P → Q :=
begin
  -- The goal is of the form `X → Y` so we can use `intro`
  intro h, -- now `h` is the hypothesis that `P` is true.
  -- Our goal is now the same as a hypothesis so we can use `exact`
  exact hQ,
end

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q :=
begin
  -- our goal is `⊢ Q` which matches with the conclusion of `h` so `apply` works
  apply h,
  -- now our goal has changed to `P` which is an assumption
  exact hP,
end

/-

## Examples for you to try

Delete the `sorry`s and replace them with comma-separated tactic proofs
using `intro`, `exact` and `apply`.

-/

/-- Every proposition implies itself. -/
example : P → P :=
begin
  sorry
end

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`. If you think
about it, this means that to deduce `R` you will need to prove both `P`
and `Q`. In general to prove `P1 → P2 → P3 → ... Pn` you can assume
`P1`, `P2`,...,`P(n-1)` and then you have to prove `Pn`. 

So the next level is asking you prove that `P → (Q → P)`.

-/
example : P → Q → P :=
begin
  sorry
end

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`. 
This is called "Modus Ponens" by logicians. -/
example : P → (P → Q) → Q :=
begin
  sorry
end

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/
example : (P → Q) → (Q → R) → (P → R) :=
begin
  sorry,
end

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
-- two goals! Note that tactics operate on only the first goal.
example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  sorry
end

-- Now they get a little harder. You can skip these if
-- you feel like you know what you're doing.

variables (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T :=
begin
  sorry
end

example : (P → Q) → ((P → Q) → P) → Q :=
begin
  sorry
end

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P :=
begin
  sorry
end

example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
begin
  sorry
end

example : (((P → Q) → Q) → Q) → (P → Q) :=
begin
  sorry
end

example :
  (((P → Q → Q) → ((P → Q) → Q)) → R) →
  ((((P → P) → Q) → (P → P → Q)) → R) →
  (((P → P → Q) → ((P → P) → Q)) → R) → R :=
begin
  sorry
end
