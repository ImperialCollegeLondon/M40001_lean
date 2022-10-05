# Logic in Lean

By "logic" here we mean the study of propositions. A proposition is a
true/false statement. For example 2+2=4, 2+2=5, and the statement
of the Riemann Hypothesis are all propositions.

In the logic part of the Introduction to University Mathematics (IUM) course
we learn about how to do basic mathematics with propositions. Basic mathematics
with numbers involves learning about how functions like `+`, `-`, `*` and `/`
interact with numbers like 0, 1, 2, .... Basic mathematics with propositions involves learning about how
functions like `→`, `¬`, `∧`, `↔` and `∨` interact with
propositions like `true` and `false`.

In Lean we can prove mathematical theorems using *tactics* such as `intro`
and `apply`. In this, the logic section of the IUM Lean resources, we will
learn how to use about ten of Lean's basic tactics. They are all explained
below, but they are also explained within the text when the need to use
them arises.

# Links for the impatient

If you just want to dive in and haven't even got Lean installed on your computer, you
can try these levels online; here are the links

* [Logic sheet 1](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet1.lean)
* [Logic sheet 2](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet2.lean)
* [Logic sheet 3](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet3.lean)
* [Logic sheet 4](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet4.lean)
* [Logic sheet 5](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet5.lean)
* [Logic sheet 6](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2FImperialCollegeLondon%2FM40001_lean%2Fmaster%2Fsrc%2F2021%2Flogic%2Fsheet6.lean)

and if you're stuck then either skip down to "Tactics you will need" or [watch a short video or two](https://www.youtube.com/playlist?list=PLVZep5wTamMmeF968ovIjd-uc1I6kdirJ) where I give an introduction to how to
get started. When you're done with these you can move onto [sets](https://github.com/ImperialCollegeLondon/M40001_lean/blob/master/src/2021/sets/README.md).

## Lean's notation for logic.

In Lean, `P : Prop` means "`P` is a proposition", and `P → Q` is the
proposition that "`P` implies `Q`". Note that Lean uses a single arrow `→`
rather than the double arrow `⇒`.

The notation `h : P` means any of the following equivalent things:

* `h` is a proof of `P`
* `h` is the assumption that `P` is true
* `P` is true, and this fact is called `h`

Here `h` is just a variable name. We will often call proofs of `P` things like `hP`
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
| `false`             | can't be used      | `exfalso, exact h`       |

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

## The `by_cases` tactic

If `P : Prop` is a true-false statement, then `by_cases hP : P` will
turn your goal into two goals, one with a hypothesis `hP : P` and
the other with a hypothesis `hP : ¬P`.

# Sheet 3 cheat sheet

Here's which tactic to try if you want to use a certain proposition as your
next move.

| Form of proposition | In the goal?       | Hypothesis named `h`?    |
|---------------------|--------------------|--------------------------|
| `¬P`                | `intro hP`         | `apply h`                |


# Tactics for sheet 4

## The `cases` tactic

`cases` is a very general-purpose tactic for "deconstructing" hypotheses.
If `h` is a hypothesis which somehow "bundles up" two pieces of information,
then `cases h with h1 h2` will make hypothesis `h` vanish and will replace it
with the two "components" which made the proof of `h` in the first place.
An example of this occurring in logic sheet 4 is `h : P ∧ Q` which is a
bundling of a proof of `P` and a proof of `Q`.

### Example

If you have a hypothesis

```
hPaQ : P ∧ Q
```

then

`cases hPaQ with hP hQ,`

will delete `hPaQ` and replace it with

```
hP : P
hQ : Q
```

## The `split` tactic

If your goal is an "and" goal:

```
⊢ P ∧ Q
```

then the `split` tactic will turn it
into *two* goals


```
⊢ P
```

and

```
⊢ Q
```

It is best practice to indicate when you are working with two goals, either by using squiggly brackets like this:

```
...
split,
{ working on P,
  end of proof of P },
{ working on Q,
  end of proof of Q },
```

or by using indentation like this:

```
split,
  working on P,
  end of proof of P,
working on Q,
...
```

# Sheet 4 cheat sheet

Here's which tactic to try if you want to use a certain proposition as your next move.

| Form of proposition | In the goal?       | Hypothesis named `h`?    |
|---------------------|--------------------|--------------------------|
| `P ∧ Q`                | `split`         | `cases h with hP hQ`     |

# Tactics for sheet 5

## The `refl` tactic.

`refl` can be used to prove a goal of the form `⊢ P ↔ P`.

(It can also be used to prove a goal of the form `⊢ P = P` but
we don't see any such goals in the logic levels because we never
see `=`)

## The `rw` tactic

If you have a hypothesis `h : P ↔ Q` then `rw h` will
replaces all `P`s with `Q`s in the goal. You can use it
on hypotheses too -- if `h : P ↔ Q` then `rw h at h1` will 
replace all `P`s with `Q`s in `h1`.

### Examples

1) If your tactic state looks like this:

```
h1 : P ↔ Q 
⊢ P → (R ∨ ¬ S) 
```

then `rw h1` will change the goal to
```
⊢ Q → (R ∨ ¬ S) 
```

This is logically valid because `h1` says that `P` and `Q` have
the same truth value, so they can be regarded as equal.
Similarly if your state contains two hypotheses

```
h1 : P ↔ Q 
h2 : P → (R ∨ ¬ S) 
```

then `rw h1 at h2` will change `h2` to 
```
h2 : Q → (R ∨ ¬ S)
```

2) If your tactic state looks like this:

```
h : P ↔ Q 
⊢ P ∨ false ↔ Q ∨ false
```

then `rw h` will *close the goal*! The reason this happens
is that the `rw` tactic optimistically tries `refl` every
time it has finished running to see if it closes the goal.
After the actual rewrite the goal in the above example
is `⊢ Q ∨ false ↔ Q ∨ false` and `refl` will close
this goal.

3) If your tactic state is
```
h : P ↔ Q 
⊢ ¬Q
```

then `rw h` will fail, because there are no
`P`s to be changed into `Q`s, and `rw` works
by default from left to right. To change the
goal from `¬Q` to `¬P`, try `rw ← h`. You
get the left arrow with `\l` (that's a little
letter L, not a number 1 or letter I).

### Note

`rw` works (**only**) with hypotheses of the
form `P ↔ Q` (or `a = b`, as will see later). A common mistake
is for users to try to use it with *implications*,
that is, hypotheses of the form `P → Q`. That is
what the `apply` tactic is for.

### Warning

As mentioned above, the `rw` tactic tries `refl` after
each invocation, so some goals might get closed earlier
than you think. 

## The `cases` and `split` tactics (again)

`P ∧ Q` and `P ↔ Q` are formally quite similar -- they both package up
two facts into one piece of information. The term `P ∧ Q` packages up
proofs of `P` and `Q`. Similarly, the term `P ↔ Q` packages up proofs
of `P → Q` and `Q → P`. 

If your goal is
```
⊢ P ↔ Q
```

then `split` will change it into two goals `⊢ P → Q` and `⊢ Q → P`.

If however you have a hypothesis
```
h : P ↔ Q
```

then `cases h with hPiQ hQiP` will change it into two hypotheses
`hPiQ : P → Q` and `hQiP :  Q → P`.

## Important note

Note however that in contrast to the `and` case, where `cases` is almost
certainly what you want to do with `h : P ∧ Q`, a bi-implication
hypothesis `h : P ↔ Q` can be used by the `rw` tactic. So knowing
when to deconstruct them is something of an art.

# Sheet 5 cheat sheet

Here's which tactic to try if you want to use a certain proposition as your next move.

| Form of proposition | In the goal?       | Hypothesis named `h`?    |
|---------------------|--------------------|--------------------------|
| `P ↔ Q`             | `split`            | `cases h...` or `rw h`   |

# Tactics for sheet 6

## `left` and `right`

If your goal is

```
⊢ P ∨ Q
```

then `left` changes the goal to `⊢ P`. The logic is that `P` implies `P ∨ Q`
so we can `apply` this implication. Similarly `right` changes the goal to `⊢ Q`

## cases (revisited)

If you have a hypothesis

```
h : P ∨ Q
```

then `cases h with hP hQ` changes your goal into two goals, one
with a hypothesis `hP : P` and the other with `hQ : Q`. The logic is
that we know that one of `P` or `Q` is true, so we can split into
two cases.

# Sheet 6 cheat sheet

Here's which tactic to try if you want to use a certain proposition as your next move.

| Form of proposition | In the goal?       | Hypothesis named `h`?    |
|---------------------|--------------------|--------------------------|
| `P ∨ Q`             | `left` or `right`  | `cases h with hP hQ`    |
