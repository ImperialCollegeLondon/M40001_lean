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

In Lean, the *definition* of `¬ P` is `P → false`, so whenever
you see `¬ P` you can replace it in your head with `P → false`,
and we already know how to deal with stuff like that from the
previous sheets.

If you don't like making that change in your head, you can
use the `change` tactic to do it for you.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ P → (P → false) :=
begin
  sorry
end
