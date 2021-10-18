# Sets

Lean uses type theory, not set theory. In short this means that
every set must be a subset of a type. For example, the real
numbers are a type in Lean, so that means we can consider sets
of real numbers (like the positive real numbers, or the prime numbers).
If you don't know what a type is -- a type is just a collection of terms,
like a set is a collection of elements -- I think of them in pretty
much the same way.
## Notation

If `X` is a type we write `(X : Type)`. The type `set X` means
the sets whose elements are in `X`, so you can these things
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