# Sets in Lean

Lean uses type theory, not set theory. In short this means that
every set must be a subset of a type. For example, the real
numbers are a type in Lean, so that means we can consider sets
of real numbers (like the positive real numbers, or the prime numbers).
If you don't know what a type is -- a type is just a collection of terms,
like a set is a collection of elements -- I think of them in pretty
much the same way. In this collection of lean problem sheets we'll learn
a few more tactics to enable us to work with sets.

## Notation

If `X` is a type we write `(X : Type)`. The type `set X` means
the sets whose elements are in `X`, so you can view these things
as subsets of `X`. If `A : set X` then `A` is a subset of `X`
and if `x : X` is a term of type `X` (i.e., an element of `X`)
then the notation `x ∈ A` means that `x` is an element of `A`.

# Links for the impatient

If you just want to dive in and haven't even got Lean installed on your computer, you
can try these levels online; here are the links

* [Sets sheet 1](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Fsets%2Fsheet1.lean)

* [Sets sheet 2](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Fsets%2Fsheet2.lean)

* [Sets sheet 3](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Fsets%2Fsheet3.lean)

* [Sets sheet 4](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Fsets%2Fsheet4.lean)

* [Sets sheet 5](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Fsets%2Fsheet5.lean)

* [Sets sheet 6](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Fsets%2Fsheet6.lean)

* [Sets sheet 7](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Fsets%2Fsheet7.lean)

and if you're stuck then either skip down to "Tactics you will need" or [watch the relevant videos in the playlist](https://www.youtube.com/playlist?list=PLVZep5wTamMmeF968ovIjd-uc1I6kdirJ).

# Tactics you will need.

To do sets problems in Lean you need to know some basic tactics.
Remember that when applying several tactics, you should put a comma
after each one.

## Tactics for sheet 1.

## The `intro` tactic.

If your goal is

```
⊢ ∀ x, <something>
```

or 
```
⊢ ∀ (x : X), <something>
```

then the tactic

`intro x,`

will turn your tactic state into
```
x : X
⊢ <something>
```

It is Lean's way of saying "let `x` be an arbitrary element of `X`"
or, more precisely, "let `x` be a term of type `X`" (different words
but same meaning)

## The `specialize` tactic

If you have hypotheses

```
x : X
h : ∀ (a : X), <something involving a>
```

then to apply the hypothesis `h` to the element `x` you can write
```
specialize h x,
```

This will turn `h` into
```
h : <something involving x>
```

with no `∀` mentioned any more.

# Sheet 1 cheat sheet

Here's which tactic to try if you want to use a certain proposition as your next move.

| Form of proposition | In the goal? | Hypothesis named `h`? |
|---------------------|--------------|-----------------------|
| `∀ (a : X), ...`    | `intro x,`   | `specialize h x,`     |

## Tactics for sheet 2.

No new tactics are needed.

## Tactics for sheet 3.

No new tactics are needed.

## Tactics for sheet 4.

### The `cases` tactic (again)

We've seen `cases` being used before to take apart `h : P ∧ Q` and
`h : P ∨ Q`. We can also use it to take apart hypotheses involving `∃`.

If `h : ∃ t : X, P t` is a hypothesis (here `P t` is any proposition
depending on a variable `t`, for example `t ∈ A`), then `cases h with x hx,`
will give us `x : X` and `hx : P x`.

### The `use` tactic

If we have a goal `⊢ ∃ x : X, P x` and a term `a : X` which we know
will work, then `use a,` will change the goal to `P a`. By the way,
`use` tries `refl` afterwards so it might magically close goals early.

| Form of proposition | In the goal? | Hypothesis named `h`? |
|---------------------|--------------|-----------------------|
| `∃ (a : X), ...`    | `use x,`     | `cases h with a ha,`  |

## Tactics for sheet 5.

No new tactics are needed. Here are some which may make your proofs shorter.

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

You can do this all in one go with `rcases h with ⟨hP, hQ, hR⟩,`. The
name `rcases` stands for "recursive cases".

`rcases` can also be used for `or` hypotheses too; here the syntax is that if
we have
```
h : P ∨ Q
```
then `rcases h with (hP | hQ),` will turn our goal into two goals, one with
`hP : P` and the other with `hQ : Q`.

Even better, `rcases` works on `h : false`. Here there are no cases at all!
So `rcases h with ⟨⟩,` solves the goal.

### The `rintro` tactic

It's quite common to find yourself doing `intro` then `cases` or,
more generally, `intro` then `rcases`. The `rintro` tactic does
these both at once! So for example if your goal is

```
⊢ (P ∧ Q) → R
```

then `rintro ⟨hP, hQ⟩,` leaves you at

```
hP : P
hQ : Q
⊢ R
```

i.e. the same as `intro h, cases h with hP hQ,`
or `intro h, rcases h with ⟨hP, hQ⟩,`.

You can introduce more than one hypothesis at once -- `rintro` generalises
`intros` as well. For example if your goal is

```
⊢ P → Q ∧ R → S
```

then `rintro hP ⟨hQ, hR⟩,` turns it into

```
hP : P
hQ : Q
hR : R
⊢ S
```

## Tactics for sheet 6.

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

## Tactics for sheet 7.

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



| Form of proposition | In the goal? | Hypothesis named `h`? |
|---------------------|--------------|-----------------------|
| `A = B`             | `ext x,`     | `rw h,`               |

