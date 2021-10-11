/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

Usage of new tactics:

1) If your goal is `⊢ P ∨ Q` then `left` will change it to `⊢ P`
and `right` will change it to `⊢ Q`.

2) If have `h : P ∨ Q` as a hypothesis then `cases h with hP hQ`
will turn your goal into two goals, with `hP : P` as a hypothesis
and the other with `hQ : Q`.

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  sorry
end

example : Q → P ∨ Q :=
begin
  sorry,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  sorry
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  sorry
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  sorry,
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  sorry,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  sorry,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  sorry,
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  sorry
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  sorry
end
