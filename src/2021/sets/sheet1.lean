/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 1 : introduction

We learn the basic interface for sets in Lean.

Tactics you will need to know for this sheet:

* `exact`
* `rw` (used with equalities)

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
  (Ω : Type) -- Everything will be a subset of `Ω`
  (A B C D E : set Ω) -- A,B,C,D,E are subsets of `Ω`
  (x y z : Ω) -- x,y,z are elements of `Ω` or, more precisely, terms of type `Ω`
/-

With propositions, we proved everything ourselves. As you can imagine,
this is not an efficient way to actually get somewhere.
Lean already has all the basic results about sets such as `A ∩ B = B ∩ A`
which we use all the time without even noticing. On this sheet we will
not learn how to *prove* these results, but we will learn how to *use*
them.

## Introduction to the `set` API

Here are the names of a few theorems about sets in Lean's maths library

`set.union_comm A B : A ∪ B = B ∪ A` 
`set.inter_comm A B : A ∩ B = B ∩ A`
`set.union_assoc A B C : A ∪ B ∪ C = A ∪ (B ∪ C)` 
-- note that A ∪ B ∪ C means (A ∪ B) ∪ C in Lean; "union is left associative".
`set.inter_assoc A B C : A ∩ B ∩ C = A ∩ (B ∩ C)`
-- Note that `→` is right associative ;-)

These lemmas are all in the `set` namespace (i.e. their full names
all begin with `set.`). It's annoying having to type `set.` all the time
so we `open set` which means you can skip it and just write `union_comm A B`

-/

open set

-- now we don't need to write `set.union_comm`, we can just write `union_comm`
example : A ∪ B = B ∪ A :=
begin
  exact union_comm A B
end

/-

## The `rw` tactic revisited

The `rewrite` or `rw` tactic can be used not just with `P ↔ Q` statements
but also with `X = Y` statements. For example, if your goal is

```
⊢ (A ∪ B) ∩ C = D
```

then the tactic `rw union_comm A B`, or just `rw union_comm` will change it to

```
⊢ (B ∪ A) ∩ C = D
```

The reason is that `union_comm A B` is a proof of `A ∪ B = B ∪ A`. 

-/

-- Try using tactics like `rw union_comm A B` or just `rw union_comm`
-- to do this example
example : (A ∪ B) ∩ C = C ∩ (B ∪ A) :=
begin
  sorry
end

/-
Note that `rw union_comm A` will change `A ∪ ?` to 
`? ∪ A` for some set `?`. You can even do `rw union_comm _ B` if you
want to change `? ∪ B` to `B ∪ ?` 

Now try these yourself.
-/
example : A ∪ B ∪ C = C ∪ B ∪ A :=
begin
  sorry
end

example : x ∈ A ∩ B ∩ C ↔ x ∈ B ∩ C ∩ A :=
begin
  sorry,
end

example : ((A ∪ B) ∪ C) ∪ D = A ∪ (B ∪ (C ∪ D)) :=
begin
  sorry
end

example : A ∪ B = C ∩ D → B ∪ A ∪ E = E ∪ (C ∩ D) :=
begin
  sorry,
end  

/-

Here are some distributivity results

`set.union_distrib_left A B C : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`
`set.union_distrib_right A B C : (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C)`
`set.inter_distrib_left A B C : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`
`set.inter_distrib_right A B C : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)`

We have `set` open so you can start the next one with e.g. 
`rw inter_distrib_left`

-/

example : (A ∪ B) ∩ (C ∪ D) = (A ∩ C) ∪ (B ∩ C) ∪ (A ∩ D) ∪ (B ∩ D) :=
begin
  sorry,
end
 
/-

## Top tip

Pretty clearly it's going to get hard to remember the names of all
the lemmas that we mathematicians use without thinking. However
you can look them up in the library. The below code

```
example : A ∩ B = B ∩ A :=
begin
  library_search
end
```

is a way of looking up names of standard lemmas (i.e. lemmas which
are already in Lean's maths library). Cut and paste the example 
below this comment to see `library_search` in action. Click on the blue output
of "Try this:" to replace `library_search` with what it found. 
-/
