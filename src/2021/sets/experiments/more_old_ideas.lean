/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 1

A lot of questions about sets can be reduced to questions about logic,
which we now know how to do in Lean.



TODO descn

Tactics you will need to know for this sheet:

* `todo`

-/

/-

All our sets on this sheet will be subsets of a big underlying set `Ω`,
which plays the role of a "universe". In Lean such a universe is
called a "type", not a set. So `Ω` will be a type, all our sets
`A`, `B`, `C` etc will be subsets of `Ω`, and all our elements
`x`, `y`, `z` etc will be what is called "terms of type `Ω`". In other
words, they may or may not be elements of `A`, `B`, `C` but they will
definitely all be elements of `Ω`.

-/

-- set up variables
variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`
/-

## More of the `set` API

Here are the names of a few theorems about sets in Lean's maths library

`antisymm : A ⊆ B → B ⊆ A → A = B`
`set.ext_iff : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B`

-/

open set

example : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B :=
begin
  rw set.subset_def, -- or refl?
end

lemma subset_refl : A ⊆ A :=
begin
  rw subset_def,
  sorry,
end

example (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ B :=
begin
  -- If you start with `rw subset_def at *` then you
  -- will have things like `hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z`
  -- You need to think of `hYZ` as a function, which has two
  -- inputs: first a term `a` of type `Ω`, and second a proof `haY` that `a ∈ Y`.
  -- It then produces one output `haZ`, a proof that `a ∈ Z`.
  -- You can also think of it as an implication:
  -- "if a is in Ω, and if a ∈ Y, then a ∈ Z". Because it's an implication,
  -- you can `apply hYZ`. This is a really useful skill!
  sorry
end

/-!

# Equality of sets

Two sets are equal if and only if they have the same elements.
The name of this theorem is `set.ext_iff`.
-/

example : A = B ↔ (∀ a, a ∈ A ↔ a ∈ B) :=
begin
  exact set.ext_iff
end

-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 


lemma subset.antisymm (hXY : A ⊆ B) (hYX : B ⊆ A) : A = B :=
begin
  -- start with `ext x`,
  sorry
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

example : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
begin
  exact set.mem_union x A B, -- or refl
end

example : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
begin
  exact set.mem_inter_iff x A B, -- or refl
end

example : A ∪ A = A :=
begin
  ext x,
  rw mem_union,
  tauto!,
end

lemma subset_union_left : A ⊆ A ∪ B :=
begin
  sorry
end

lemma subset_union_right : B ⊆ A ∪ B :=
begin
  sorry
end

example : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C :=
begin
  sorry
end

example (hAB : A ⊆ B) (hCD : C ⊆ D) : A ∪ C ⊆ B ∪ D :=
begin
  sorry
end

example (hAB : A ⊆ B) : A ∪ C ⊆ B ∪ C :=
begin
  sorry
end

example : A ∩ B ⊆ A :=
begin
  sorry
end

-- don't forget `ext` to make progress with equalities of sets

example : A ∩ A = A :=
begin
  sorry
end

example : A ∩ B = B ∩ A :=
begin
  sorry
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  sorry
end

/-!

### Forall and exists

-/

example : ¬ (∃ x, x ∈ A) ↔ ∀ y, ¬ (y ∈ A) :=
begin
  sorry,
end

example : ¬ (∀ x, x ∈ A) ↔ ∃ y, ¬ (y ∈ A) :=
begin
  sorry,
end


