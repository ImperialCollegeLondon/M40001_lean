/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔ `)

We learn about how to manipulate `P ↔ Q` in Lean.

You'll need to know about the tactics from the previous sheets,
and it will make your life much easier if you also know the
following tactic:

* `refl`
* `rw`

Rules of thumb: 

If your goal is `P ↔ P` then `refl` will solve it.

If `hPiQ : P ↔ Q` is a hypothesis, you can decompose it
using `cases hPiQ with hPQ hQP`. However, if you keep
it around then you can do `rw hPiQ` which changes all `P`s to `Q`s.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ↔ P :=
begin
  sorry
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  sorry
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  sorry
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  sorry
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  sorry
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  sorry
end

example : ¬ (P ↔ ¬ P) :=
begin
  sorry,
end
