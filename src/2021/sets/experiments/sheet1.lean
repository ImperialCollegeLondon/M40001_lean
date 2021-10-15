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

Tactics you will need to know for this sheet:

* `ext`

-/

/-

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


-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 

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

open set

example : A ∪ A = A :=
begin
  ext x,
  rw mem_union,
  tauto!,
end

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
  ext x,
  rw mem_inter_iff, -- simp only
  rw mem_inter_iff,
  rw mem_inter_iff,
  rw mem_inter_iff,
  tauto!,
end

/-!

### Forall and exists

-/

example : ¬ (∃ x, x ∈ A) ↔ ∀ y, ¬ (y ∈ A) :=
begin
  split,
    -- intro for forall
    intros h y hyA,
    apply h,
    -- use eliminates exists
    use y,
    assumption,
  intro h,
  intro hex,
  -- cases on exists
  cases hex with x hxA,
  -- new tactic
  specialize h x,
  apply h,
  assumption,
end

example : ¬ (∀ x, x ∈ A) ↔ ∃ y, ¬ (y ∈ A) :=
begin
  split,
    intro h,
    by_contra h2,
    apply h,
    intro x,
    by_contra h3,
    apply h2,
    -- use for exists
    use x,
  intro h,
  -- cases on exists
  cases h with x hx,
  intro h,
  -- ∉ is ¬ (x ∈ A)
  apply hx,
  exact h x, -- forall is a function
end


