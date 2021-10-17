/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 4 : exists (`∃`)

In this sheet we learn how to manipulate `∃` in Lean. We will see
statements of the form `∃ x, x ∈ A`. We will need to learn two new
tactics -- one for making progress when the goal is `⊢ ∃ x, x ∈ A`, 
and one for making progress when we have a hypothesis `h : ∃ x, x ∈ A`.

## New tactics you will need to know

`cases` or `rcases` -- to get the `x` from a hypothesis `h : ∃ x, ...`
`use` -- to make progress on goals of the form `⊢ ∃ x, ...`

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- TODO
