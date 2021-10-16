/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.set.basic

/-!

# Sets in Lean, example sheet 2 : the empty set and the "universal set".

We know what the empty subset of `X` is, and the Lean notation for
it is `∅`, or, if you want to say which type we're the empty subset
of, it's `∅ : set X`. 

At the other extreme, the subset of `X` containing all the terms of type `X`
is...well...mathematicians would just call it `X`, but `X` is a type, and
if we want a set it's called `set.univ : set X`, or just `univ : set X` if
we have opened the `set` namespace. Let's do that now.

-/

--open set

-- set up variables
variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

/-

If `x : X` then `x ∈ ∅` is *by definition* `false`, and `x ∈ univ` is
*by definition* `true`. 

-/

example (X : Type) (A : set X) : A = { x : X | x ∈ A } := rfl

open set

-- TODO -- ask on Zulip about why autocomplete doesn't work if `open set`
-- and `set.mem_empty`

example : x ∈ (∅ : set X) = false :=
begin
  rw set.mem_empty,
end

example : set X = (X → Prop) := rfl

theorem foo (P Q : Prop) : (P ↔ Q) ↔ (P = Q) :=
begin
  simp only [eq_iff_iff],
end


#print axioms foo


#exit
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