/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 1

We learn about propositions, and implications `P → Q` between them. You can get
this arrow by typing `\to` or `\r`. Mathematicians usually write the
implication arrow as `P ⇒ Q` but Lean prefers a straightforward single arrow.

To solve the levels on this sheet you will need to know how to use the
following tactics:

* `intro`
* `exact`
* `apply`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

/- 

## Level 1 : implies

-/

/-- Every proposition implies itself. -/
lemma identity : P → P :=
begin
  intro hp,
  exact hp,
end

/-

Note that `→` is not associative: in general `P → (Q → R)` and `(P → Q) → R`
might not be equivalent. This is like subtraction on numbers -- in general
`a - (b - c)` and `(a - b) - c` might not be equal.

So if we write `P → Q → R` then we'd better know what this means.
The convention in Lean is that it means `P → (Q → R)`.

-/
example : P → Q → P :=
begin
  intros hP hQ,
  exact hP,
end

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`. -/
lemma modus_ponens : P → (P → Q) → Q :=
begin
  intros hP hPQ,
  apply hPQ,
  exact hP,
end

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/
lemma transitivity : (P → Q) → (Q → R) → (P → R) :=
begin
  intros hPQ hQR hP,
  apply hQR,
  apply hPQ,
  exact hP,
end

example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  intros hPQR hPQ hP,
  apply hPQR,
  { exact hP },
  { apply hPQ,
    exact hP },  
end

-- Now they get a little harder

variables (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T :=
begin
  intros hPR hSQ hRT hQR hS,
  apply hRT,
  apply hQR,
  apply hSQ,
  exact hS,
end

example : (P → P → Q) → ((P → Q) → P) → Q :=
begin
  intros hPPQ hPQP,
  apply hPPQ,
  { apply hPQP,
    intro hP,
    apply hPPQ,
    { exact hP },
    { exact hP } },
  { apply hPQP,
    intro hP,
    apply hPPQ,
    { exact hP },
    { exact hP } },
end

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P :=
begin
  intros hPQR hQRP hRPQ,
  apply hQRP,
  intro hQ,
  apply hPQR,
  intro hP,
  apply hRPQ,
  intro hR,
  exact hP,
end

example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
begin
  intros hQPP hQR hRP,
  apply hQPP,
  intro hQ,
  apply hRP,
  apply hQR,
  exact hQ,
end

example : (((P → Q) → Q) → Q) → (P → Q) :=
begin
  intros hPQQQ hP,
  apply hPQQQ,
  intros hPQ,
  apply hPQ,
  exact hP,
end

example :
  (((P → Q → Q) → ((P → Q) → Q)) → R) →
  ((((P → P) → Q) → (P → P → Q)) → R) → 
  (((P → P → Q) → ((P → P) → Q)) → R) → R :=
begin
  intros h1 h2 h3,
  apply h2,
  intros hPPQ hP hP2,
  apply hPPQ,
  intro hP3,
  exact hP,
end