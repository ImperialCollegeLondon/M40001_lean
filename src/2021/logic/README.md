# Logic

By "logic" here we mean the study of propositions. A proposition is a
true/false statement. For example 2+2=4, 2+2=5, and the statement
of the Riemann Hypothesis are all propositions.

In the logic part of the Introduction to University Mathematics (IUM) course
we learn about how to do basic mathematics with propositions. Basic mathematics
with numbers involves learning about how functions like `+`, `-`, `*` and `/`
interact with numbers like 0, 1, 2, .... Basic mathematics with propositions involves learning about how
functions like `→`, `¬`, `∧`, `↔` and `∨` interact with
propositions like `true` and `false`.

# Links for the impatient

If you just want to dive in and haven't even got Lean installed on your computer, you
can try these levels online; here are the links

* [Logic sheet 1](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet1.lean)
* [Logic sheet 2](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet2.lean)
* [Logic sheet 3](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet3.lean)

and if you're stuck then either skip down to "Tactics you will need" or watch a short video (to be uploaded) where I give an introduction to how to
get started.

## Lean's notation for logic.

In Lean, `P : Prop` means "`P` is a proposition", and `P → Q` is the
proposition that "`P` implies `Q`". Note that Lean uses a single arrow `→`
rather than the double arrow `⇒`.

The notation `h : P` means any of the following equivalent things:

* `h` is a proof of `P`
* `h` is the assumption that `P` is true
* `P` is true, and this fact is called `h`

Here `h` is a variable. We will often call proofs of `P` things like `hP`
but you can call them pretty much anything.

WARNING: do not confuse `P : Prop` with `hP : P`. The former just means
that `P` is a true-false statement; the latter means that it is a true
statement.

## Lean's tactic state.

Lean's "tactic state", or "local context", is what you see on the right
hand side of the screen when you have Lean up and running. In the middle
of a proof it might look something like this:

```
P Q : Prop
hP : P
hPQ : P → Q
⊢ Q
```

The proposition after the "sideways T" at the bottom is the thing you
are supposed to be *proving* -- this is the *goal* of the level of
the game. The stuff above that weird T is the stuff you are *assuming*.
In the example above, `P` and `Q` are propositions, and we are assuming
that `P` is true and that `P` implies `Q`, and we are supposed to be
proving that `Q` is true. If you succeed in proving the goal, Lean
will display a "goals accomplished 🎉" message and, assuming you
didn't use `sorry` at any point (which is cheating), you've solved the level.

How then do we manipulate the tactic state? We do this using tactics,
which you type in on the left hand side of the screen.

# Tactics you will need.

To do logic problems in Lean you need to know some basic tactics.
Remember that when applying several tactics, you should put a comma
after each one.

## Tactics for sheet 1.

## The `intro` tactic.

If your goal is

```
⊢ P → Q
```

then the tactic

`intro hP,`

will turn your tactic state into

```
hP : P
⊢ Q
```

Variant: `intros` can be used to introduce
more than one assumption at once. Don't forget
to name your hypotheses, e.g. `intros hP hQ` if your goal is `P → Q → <something else>`.

## The `exact` tactic

If your tactic state is

```
hP : P
⊢ P
```

then the tactic

`exact hP,`

will close your goal.

Note: `exact P` does not work. Don't confuse
the *statement* `P` with its *proof* `hP`.

Variant: The `assumption` tactic closes a goal if its proof is any one of the assumptions
in the tactic state. 

## The `apply` tactic

If your tactic state is

```
hPQ : P → Q
⊢ Q
```

then the tactic

`apply hPQ,`

will change it to

```
hPQ : P → Q
⊢ P
```

The `apply` tactic is useful for *arguing backwards*. It reduces the goal to a potentially easier goal, without changing any hypotheses.

# Sheet 1 cheat sheet

Here's which tactic to try if you want to use a certain proposition as your next move.

| Form of proposition | In the goal? | Hypothesis named `h`? |
|---------------------|--------------|-----------------------|
| `P → Q`             | `intro hP`   |             `apply h` |

# Tactics for sheet 2

## The `trivial` tactic

If your goal is

```
⊢ true
```

then you can prove it with `trivial`.

Note that if you have a hypothesis `h : true` then this is useless to you,
because a true hypothesis is obviously true.

## The `exfalso` tactic

If your goal is

```
⊢ <anything at all>
```

then the `exfalso` tactic changes it to 

```
⊢ false
```

What is going on here? Note that `false → true` and `false → false` are both
true, which means that `false → P` for any proposition `P`. `apply`ing this
fact, we can change any goal we like to `false`, and this is what the
tactic does.

A useful technique: if you have a *hypothesis* `h : false`:

```
h : false
⊢ <anything at all>
```

then you can solve the level with `exfalso` followed by `exact h`.

# Sheet 2 cheat sheet

Here's which tactic to try if you want to use a certain proposition as your next move.

| Form of proposition | In the goal?       | Hypothesis named `h`?    |
|---------------------|--------------------|--------------------------|
| `true`              | `trivial`          | can't be used            |
| `false`             | can't be used      | `exfalso` then `exact h` |

# Tactics for sheet 3

## The `change` tactic

Perhaps surprisingly, equality is a complicated thing. But one
of the simplest versions of equality is *definitional equality*.
In Lean, `¬ P` is *defined to mean* `P → false`, for example.
The `change` tactic can be used to change a term to another
term which is equal *by definition*. Here are two examples.

1) If your goal is

```
⊢ ¬ P
```

then the tactic
```
change P → false
```

will change your goal to

```
⊢ P → false
```

2) If you have a hypothesis

```
h : ¬ P
```

then the tactic

```
change P → false at h
```

will change the hypothesis to

```
h : P → false
```

Note however that often you *do not have to use this tactic*. For
example if your tactic state is

```
h : ¬ P
⊢ false
```

then `apply h` will *just work* and will change the goal to `P`,
because `h` is *by definition* equal to `P → false`.

## The `by_contra` tactic

If your goal is

```
⊢ P
```

then `by_contra h` will change your tactic state to

```
h : ¬P
⊢ false
```

It is a "proof by contradiction" tactic. 
