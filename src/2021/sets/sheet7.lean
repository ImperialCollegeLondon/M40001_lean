/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 7 : the sets API

It might have occurred to you that if you had a prove
things like commutativity of `∩` every time you needed it,
then things would get boring quite quickly. 

Fortunately, the writers of Lean's mathematics library
already proved these things and *gave the proofs names*.
On the previous sheet you showed that you could do these
things yourself, so on this sheet I'll tell you the names
of the Lean versions of the proofs, and show you how to use them.

Here are some examples of proof names in Lean.

`set.union_comm A B : A ∪ B = B ∪ A` 
`set.inter_comm A B : A ∩ B = B ∩ A`
-- note `A ∪ B ∪ C` means `(A ∪ B) ∪ C` 
`set.union_assoc A B C : A ∪ B ∪ C = A ∪ (B ∪ C)` 
 -- similar comment for `∩`
`set.inter_assoc A B C : A ∩ B ∩ C = A ∩ (B ∩ C)`

(A technical point: note that `∪` and `∩` are "left associative",
in contrast to `→` which is right associative: `P → Q → R` means `P → (Q → R)`).

These lemmas are all in the `set` namespace (i.e. their full names
all begin with `set.`). It's annoying having to type `set.` all the time
so we `open set` which means you can skip it and just write things
like `union_comm A B`.

Note that `union_comm A B` is the *proof* that `A ∪ B = B ∪ A`.
In the language of type theory, `union_comm A B` is a 
"term of type `A ∪ B = B ∪ A`". Let's just compare this with what we
were seeing in the logic sheet:

```
P : Prop -- P is a proposition
hP : P -- hP is a proof of P
```

Similarly here we have 
```
A ∪ B = B ∪ A : Prop -- this is the *statement*
union_comm A B : A ∪ B = B ∪ A -- this is the *proof*
```

## New tactics you will need

* `rw` ("rewrite")

### The `rw` tactic (again)

We've seen `rw h,` being used if `h : P ↔ Q`; it changed all `P`s to `Q`s
in the goal. But `rw h,` also works for `h : A = B` -- it changes all
`A`s to `B`s in the goal. So `rw` is a "substitute in" command. 

After the substitution has occurred, Lean tries `refl` just to see if it works.
For example if `A`, `B`, `C` are sets, and our context is

```
h : A = B
⊢ A ∩ C = B ∩ C
```

then `rw h` changes the goal into `B ∩ C = B ∩ C` and then solves
the goal automatically, because `refl` works.

`rw` doesn't just work for hypotheses -- if there is a theorem 
in Lean's maths library (like `inter_comm A B`, which is a proof
that `A ∩ B = B ∩ A`) then you can `rw inter_comm A B` and it
will change `A ∩ B` in the goal to `B ∩ A`.

`rw` is a smart tactic. If the goal is

```
⊢ (A ∪ B) ∩ C = D
```

and you want to change it to `⊢ (B ∪ A) ∩ C = D` then you don't
have to write `rw union_comm A B`, you can write `rw union_comm`
and Lean will figure out what you meant. You can also write
`rw union_comm A` or even `rw union_comm _ B` if you want to give
it hints about exactly which union to commute.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- You can solve this one with `exact union_comm A B` or `rw union_comm`
example : A ∪ B = B ∪ A :=
begin
  sorry
end

example : (A ∪ B) ∩ C = C ∩ (B ∪ A) :=
begin
  sorry
end

/-
Note that `rw union_comm A` will change `A ∪ ?` to 
`? ∪ A` for some set `?`. You can even do `rw union_comm _ B` if you
want to change `? ∪ B` to `B ∪ ?` 
-/

example : A ∪ B ∪ C = C ∪ B ∪ A :=
begin
  sorry
end

example : x ∈ A ∩ B ∩ C ↔ x ∈ B ∩ C ∩ A :=
begin
  sorry
end

example : ((A ∪ B) ∪ C) ∪ D = A ∪ (B ∪ (C ∪ D)) :=
begin
  sorry
end

example : A ∪ B = C ∩ D → B ∪ A ∪ E = E ∪ (C ∩ D) :=
begin
  sorry
end  

/-

Here are some distributivity results. 

`set.union_distrib_left A B C : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`
`set.union_distrib_right A B C : (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C)`
`set.inter_distrib_left A B C : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`
`set.inter_distrib_right A B C : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)`

Which ones will you use to do the following? Note that because of the `open set`
line much earlier, you don't have to write the `set.` part of the name.

-/

example : (A ∪ B) ∩ (C ∪ D) = (A ∩ C) ∪ (B ∩ C) ∪ (A ∩ D) ∪ (B ∩ D) :=
begin
  sorry
end
 
/-

## Top tips

How the heck are we supposed to remember all the names of these lemmas
in Lean's maths library??

Method 1) There is a logic to the naming system! You will slowly
get used to the logic.

Method 2) Until then, just use the `library_search` tactic
to look up proofs. 

If you run the below code

```
example : A ∩ B = B ∩ A :=
begin
  library_search
end
```

you'll see some output on the right hand side of the screen containing
the name of the lemma which proves this example.

-/
