/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 1 : "forall" (`∀`)

A lot of questions about sets can be reduced to questions about logic.
We explain how to do this in Lean.

All the sets we consider on this and the next few sheets will all be
subsets of an underlying set `X`, which is our "universe" where all
the maths we do will take place. This underlying set `X` is called a "type" in
Lean. It plays the role of a "universe" -- every element we consider will
always be an element of `X`, and every subset we consider will
be a subset of `X`.

Notation: elements of `X` are called *terms* of the type `X` and the
notation is `x : X`. All the variables `x`, `y` and `z` which appear in this
sheet will always be terms of type `X`, i.e. elements of the set `X`
if you want to think set-theoretically.

All the sets `A`, `B`, `C` etc we consider will be subsets of `X`. 
If `x : X` then `x` may or may not be an element of `A`, `B`, `C`,
but it will always be an element of `X`.

## Tactics

Tactics you will need to know for this sheet:

* `intro` (it works for `∀` goals as well as for `P → Q`)
* `specialize`

### The `intro` tactic

If the goal is `∀ x, P(x)` then `intro a,` lets `a` be an arbitrary
element of `X` (or, more precisely, an arbitrary term of type `X`)
and changes the goal to `P(a)`.

### The `specialize` tactic

If we have a hypothesis `h : ∀ x, P(x)` and we have a term `a : X`
then `specialize h a,` changes `h` to `h : P(a)`.

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

example : (∀ x, x ∈ A ∧ x ∈ B) → (∀ y, y ∈ B ∧ y ∈ A) :=
begin
  sorry
end

example : (∀ x, x ∈ A → x ∈ B) → (∀ y, y ∈ B → y ∈ C) →
  (∀ z, z ∈ A → z ∈ C) :=
begin
  sorry
end