/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 5 : subset (`⊆`), union (`∪`) and intersection (`∩`)

In this sheet we learn how to manipulate `⊆`, `∪` and `∩` in Lean.

Here are some mathematical facts:

`A ⊆ B` is equivalent to `∀ x, x ∈ A → x ∈ B`;
`x ∈ A ∪ B` is equivalent to `x ∈ A ∨ x ∈ B`;
`x ∈ A ∩ B` is equivalent to `x ∈ A ∧ x ∈ B`. 

All of these things are true *by definition* in Lean, which means
that you can switch from one to the other with `change`, or you
can just treat something on the left hand side as if it said
what it said on the right hand side.

For example if your goal is `⊢ x ∈ A ∩ B` then you could write
`change x ∈ A ∧ x ∈ B,` to change the goal to `⊢ x ∈ A ∧ x ∈ B`, but you can
also use the `split,` tactic directly, and this will immediately turn the goal
into two goals `⊢ x ∈ A` and `⊢ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ⊆ A :=
begin
  sorry,
end

example : ∅ ⊆ A :=
begin
  sorry,
end

example : A ⊆ univ :=
begin
  sorry,
end

example : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  sorry,
end

example : A ⊆ A ∪ B :=
begin
  sorry,
end

example : A ∩ B ⊆ A :=
begin
  sorry,
end

example : A ⊆ B → A ⊆ C → A ⊆ (B ∩ C) :=
begin
  sorry,
end

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
begin
  sorry,
end

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
begin
  sorry,
end

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D :=
begin
  sorry,
end
