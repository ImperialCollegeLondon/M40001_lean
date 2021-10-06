/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `change` (optional)
* `by_contra`

Rules of thumb
1) If your goal is `⊢ ¬ P` then `change P → false` will
change it to `P → false`. Similarly if you have a hypothesis
`h : ¬ P` then `change P → false at h` will change it. Note
though that this is just for psychological purposes!

2) If your goal is `⊢ P` and you want to prove it by contradiction,
`by_contra h` will change the goal to `false` and add a hypothesis
`h : ¬ P`.

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