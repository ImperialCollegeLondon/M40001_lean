/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal. 

## Tactics 

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ⊆ B → B ⊆ A → A = B :=
begin
  sorry
end

example : A ∪ A = A :=
begin
  sorry
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
  sorry
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  sorry
end