# Logic

By "logic" here we mean the study of propositions. A proposition is a
true/false statement. For example 2+2=4, 2+2=5, and the statement
of the Riemann Hypothesis are all propositions.

In the logic part of the Introduction to University Mathematics (IUM) course
we learn about how to do basic mathematics with propositions. Basic mathematics
with numbers involves learning about how functions like `+`, `-`, `*` and `/`
interact with numbers like 0, 1, 2, .... Basic mathematics with propositions involves learning about how `→`, `¬`, `∧`, `↔` and `∨` interact with
propositions like `true` and `false`.

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
to name your hypotheses, e.g. `intros hP hQ`.

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

Note: The `assumption` tactic will also work. That means "solve the goal,
because its proof is one of our assumptions". 

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

## Sheet 1 cheat sheet

Here's which tactic to use in order to make progress with a given proposition.

| Form of proposition | In the goal? | Hypothesis named `h`? |
|--------------|-----------|------------|
| P → Q | `intro hP` | `apply h` |

## Tactics for sheet 2

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

*******************************************************

TODO

## The `rw` tactic

The "rewrite" tactic can be used to "substitute in". The syntax is `rw h`, where `h` can be
either a local hypothesis, or a theorem.
However, `h` **must**  be either an equality or a bi-implication (an "iff"). You can use it on goals, but also on hypotheses (by adding `at`).

### Examples

1) If your tactic state is 

```
h : a = b
⊢ a + 1 = 37
```

then `rw h` will change it to
```
h : a = b
⊢ b + 1 = 37
```

2) If your assumptions contain 

```
h1 : P ↔ Q 
h2 : P → (R ∨ ¬ S) 
```

then `rw h1 at h2` will change them to
```
h1 : P ↔ Q 
h2 : Q → (R ∨ ¬ S) 
```

3) If `not_iff_imp_false` is a proof
of `¬ P ↔ (P → false)` and your goal
is 

```
⊢ ¬P → Q
```

then `rw not_iff_imp_false` will change
your goal to

```
⊢ (P → false) → Q
```

4) If your tactic state is
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
form `a = b` or `P ↔ Q`. A common mistake
is for users to try to use it with *implications*,
that is, hypotheses of the form `P → Q`. That is
what the `apply` tactic is for.

### Warning

The `rw` tactic tries `refl` 

## The `by_contra` tactic

If your goal is

```
⊢ P
```

then `by_contra h,` will change your tactic state to

```
h : ¬P
⊢ false
```

It is a "proof by contradiction" tactic. Constructive mathematicians reject this tactic. We will not be talking about constructive mathematics in this course. One or two of
the exercises need it.

## The `cases` tactic

`cases` is a very general-purpose
tactic for deconstructing hypotheses. If `h` is a hypothesis which 
somehow "bundles up" two pieces of information, then
`cases h with h1 h2` will make hypothesis `h` vanish and will replace it with the two "components" which made the proof of `h` in the first place.

### Examples

1) If you have a hypothesis

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

2) If you have a hypothesis

```
hPiQ : P ↔ Q
```

then

`cases hPiQ with hPQ hQP,`

will delete `hPiQ and replace it with the two hypotheses
```
hPQ : P → Q
hQP : Q → P
```

Note however that hypotheses of the form `h : P ↔ Q` are rather useful, because you can use `rw h` tactic with them. So think twice about destroying them.


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

Similarly if your goal is `⊢ P ↔ Q` then `split,` will turn it into two goals `⊢ P → Q` and `⊢ Q → P`.

## The `left` and `right` tactics

If your goal is

```
⊢ P ∨ Q
```

then the `left` tactic will change it to

```
⊢ P
```

and the `right` tactic will change it to

```
⊢ Q
```

Note that these tactics are "dangerous" in the
sense that they can change a true goal into
a false one, and hence can stop you solving
a level. Use them wisely!

### The `have` tactic

The `have` tactic needs to be used far less
than a mathematician thinks. It is a tactic
which can be used to add a new hypothesis
to the tactic state. Of course, you will
have to prove it! Say your tactic state is

```
hQ : Q
⊢ P
```

and you decide that it would be helpful
to have a hypothesis `h : P ↔ Q` in your
list of hypotheses. You know how to prove it
from the hypotheses you have, 
but it's not there, and it's not your goal
so you can't work on it. If you type

`have h : P ↔ Q` 

then you will have _two_ goals. The first
will have all your old hypotheses, but a new
goal of `P ↔ Q`.

```
hQ : Q
⊢ P ↔ Q
```

The second will have all your old hypotheses, and the new one `h : P ↔ Q`, and you'll be back to your old goal:

```
hQ : Q
hPQ : P ↔ Q
⊢ P
```

### The `by_cases` tactic

If `P` is a proposition, then sometimes it's convenient to split
into the two cases where either `P` is true, or `¬P` is true.
The `by_cases h : P` tactic does just this; it turns one goal
into two, one with `h : P` and the other with `h : ¬P`.

### The `tauto!` tactic

OK so I left this one until the end but actually Lean has a "write down
the truth table" tactic, which solves all the levels automatically.

Say the goal is

```
⊢ <any true goal in logic at all>
```

Then `tauto!` will solve it. Where's the fun in that though!

## Notation

In Lean, `P : Prop` means "`P` is a proposition" and `P → Q` is the
proposition that "`P` implies `Q`". Note that Lean uses a single arrow `→`
rather than the double arrow `⇒`, for reasons we will learn about later.

The notation `h : P` means that `h` is a proof of `P`, and in particular
it means that `P` is true. Note that `P : Prop` just means that `P`
is a true-false statement; it does not necessarily mean that `P` is true. 

## Let's get started

Let's run through our first Lean proof. Let's figure out how to prove
that if `P` is a proposition, then `P` implies `P`. Lean turns a maths
question like this into a level of a puzzle game. Let's first set up
the level. It looks like this:

```
example (P : Prop) : P → P :=
begin
  sorry
end
```

The game is to replace the `sorry` with a proof. 
