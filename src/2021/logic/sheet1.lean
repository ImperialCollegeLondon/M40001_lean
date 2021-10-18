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

## Tactics you will need

To solve the levels on this sheet you will need to know how to use the
following tactics:

* `intro`
* `exact`
* `apply`

### intro

If your goal is `⊢ P → Q` then `intro hP,` will intrduce a
hypothesis `hP : P` and change the goal to `⊢ Q`.

### exact

If your goal is `⊢ P` and you have a hypothesis `h : P`
then `exact h,` will solve it.

### apply

If your goal is `⊢ Q` and you have `h : P → Q` then `apply h,` will
change the goal to `⊢ P`.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

-- Here are the levels. Delete the `sorry`s and replace them with
-- comma-separated tactic proofs.

/-- Every proposition implies itself. -/
example : P → P :=
begin
  sorry
end

/-

The solution to this level: 

example : P → P :=
begin
  intro hP,
  exact hP,
end

-/

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`.

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

example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  sorry
end

-- Now they get a little harder

variables (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T :=
begin
  sorry
end

example : (P → P → Q) → ((P → Q) → P) → Q :=
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
