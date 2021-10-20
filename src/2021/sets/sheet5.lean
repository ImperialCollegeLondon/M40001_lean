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

## New tactics you will need

You don't need to know any new tactics to solve this sheet. I've mentioned
the `change` tactic. You don't have to use it, and if you use it your
proofs will get longer. So in return I'll tell you about two other
tactics, `rcases` and `rintro`, which you don't have to use either
but if you use them they'll make your proofs shorter.

### The `rcases` tactic

`rcases` is a souped-up version of `cases`. It has slightly different
syntax. If you have a hypothesis `h : P ∧ Q` then `cases h with hP hQ`
and `rcases h with ⟨hP, hQ⟩` do the same thing. However, if you
have a hypothesis `h : P ∧ Q ∧ R` then Lean interprets it as `P ∧ (Q ∧ R)`
so if you want to destruct it with `cases` you have to do

```
cases h with hP hQR,
cases hQR with hQ hR
```

You can do this all in one go with `rcases h with ⟨hP, hQ, hR⟩`. The
name `rcases` stands for "recursive cases".

### The `rintro` tactic

It's quite common to find yourself doing `intro` then `cases` or,
more generally, `intro` then `rcases`. The `rintro` tactic does
these both at once! So for example if your goal is

```
⊢ (P ∧ Q) → R
```

then `rintro ⟨hP, hQ⟩` leaves you at

```
hP : P
hQ : Q
⊢ R
```

i.e. the same as `intro h, cases h with hP hQ,`

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
