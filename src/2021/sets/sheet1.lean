/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 1 : "forall" (`∀`)

A lot of questions about sets can be reduced to questions about logic.
We explain how to do this in Lean.

Tactics you will need to know for this sheet:

* `intro` (it works for `∀` goals as well as for `P → Q`)
* `specialize`

All our sets on this sheet will be subsets of a big underlying set `X`,
which plays the role of a "universe". In Lean such a universe is
called a "type", not a set. So `X` will be a type, all our sets
`A`, `B`, `C` etc will be subsets of `X`, and all our elements
`x`, `y`, `z` etc will be what is called "terms of type `X`". In other
words, they may or may not be elements of `A`, `B`, `C` but they will
definitely all be elements of `X`.

-/

-- set up variables
variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- You can start this one with `intro x`
example : ∀ x : X, x ∈ A → x ∈ A :=
begin
  sorry,
end

example : ∀ x : X, (x ∈ A ∧ x ∈ B) → x ∈ A :=
begin
  sorry
end

-- for this one if you start with `intros h x` then you might well
-- need `specialize h x` later on. This is how to use hypotheses with `∀` in.
example : (∀ x, x ∈ A ∧ x ∈ B) → (∀ x, x ∈ A) :=
begin
  sorry
end

example : (∀ x, x ∈ A ∧ x ∈ B) → (∀ x, x ∈ B ∧ x ∈ A) :=
begin
  sorry
end

example : (∀ x, x ∈ A ∨ x ∈ B) → (∀ y, y ∈ B ∨ y ∈ A) :=
begin
  sorry
end