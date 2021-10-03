/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones:

* `trivial`
* `cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : true :=
begin
  sorry
end

example : true → true :=
begin
  sorry
end

example : false → false :=
begin
  sorry
end

example : false → true :=
begin
  sorry
end

example : (true → false) → false :=
begin
  sorry
end

example : false → P :=
begin
  sorry,
end

example : true → false → true → false → true → false :=
begin
  sorry
end

example : P → ((P → false) → false) :=
begin
  sorry
end

example : (P → false) → P → Q :=
begin
  sorry
end

example : (true → false) → P :=
begin
  sorry
end