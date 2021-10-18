/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *the same thing* and can be used interchangeably. You can change
from one to the other for free.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `change` (optional)
* `by_contra`
* `by_cases`

### The `change` tactic

The `change` tactic changes a goal to a goal which
is *equal to it by definition*. The example you need to know
is that `¬ P` and `P → false` are equal by definition.

If your goal is `⊢ ¬ P` then `change P → false,` will
change it to `P → false`. Similarly if you have a hypothesis
`h : ¬ P` then `change P → false at h,` will change it to `h : P → false`.

Note that this tactic is just for psychological purposes. If you finish
a proof which uses this tactic, try commenting out the `change` lines
and note that it doesn't break.

### The `by_contra` tactic

If your goal is `⊢ P` and you want to prove it by contradiction,
`by_contra h,` will change the goal to `false` and add a hypothesis
`h : ¬ P`.

### The `by_cases` tactic

If `P : Prop` is a true-false statement then `by_cases hP : P,`
turns your goal into two goals, one with hypothesis `hP : P`
and the other with hypothesis `hP : ¬ P`.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ P → (P → false) :=
begin
  sorry,
end

example : ¬ true → false :=
begin
  sorry
end

example : false → ¬ true :=
begin
  sorry
end

example : ¬ false → true :=
begin
  sorry
end

example : true → ¬ false :=
begin
  sorry
end

example : false → ¬ P :=
begin
  sorry
end

example : P → ¬ P → false :=
begin
  sorry
end

example : P → ¬ (¬ P) :=
begin
  sorry
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry
end

example : ¬ ¬ false → false :=
begin
  sorry
end

example : ¬ ¬ P → P :=
begin
  sorry
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  sorry,
end