# Logic

By "logic" here we mean the study of propositions. A proposition is a
true/false statement. For example 2+2=4, 2+2=5, and the statement
of the Riemann Hypothesis are all propositions.

In the logic part of the Introduction to University Mathematics (IUM) course
we learn about how to do basic mathematics with propositions. Basic mathematics
with numbers involves learning about how `+`, `-`, `*` and `/` interact.
Basic mathematics with propositions involves learning
about how `→`, `¬`, `∧`, `↔` and `∨` interact.

## Logic in Lean




# Logic

Basic logic in IUM is easy. Any question at all can just be answered with
"draw a truth table". This approach is called an *extensional* approach,
where the meaning of a proposition is no more than whether it is true
or false. 

But there is another, *intensional*, way to approach these logic questions.
Here a proposition is regarded as more than just its truth value. A
mathematician clearly sometimes thinks about propositions intensionally.
For example, an extensional view on Fermat's Last Theorem is that it
is the same as 2+2=4, because both of them are true. However, one of them
took 350 years to prove, and the other is easy.

Let's take a look at logic done in a more intensional way, where
we interpret "`P` implies `Q`" not just as some value we can look up in
a table, but as the statement "if `P` is true, then `Q` is true", and
we can try and prove it by deducing `Q` from `P`. 

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
