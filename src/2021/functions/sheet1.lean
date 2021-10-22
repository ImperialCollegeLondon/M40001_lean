/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Functions in Lean, example sheet 1 : ???

???

## Tactics

???

-/

open function

 -- Our functions will go between these sets, or Types as Lean calls them
variables (X Y Z : Type)

theorem injective_def (f : X → Y) : 
  injective f ↔ ∀ (a b : X), f a = f b → a = b :=
begin
  refl -- this proof works, because `injective f` 
       -- means ∀ a b, f a = f b → a = b *by definition*
       -- so the proof is "it's reflexivity of `↔`"
end

-- similarly this is the *definition* of `surjective f`
theorem surjective_def (f : X → Y) : 
  surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
begin
  refl
end

-- similarly the *definition* of `id x` is `x`
theorem id_eval (x : X) :
  id x = x :=
begin
  refl
end

-- now let's prove some theorems
example : injective (id : X → X) :=
begin
  -- you can start with `rw injective_def` if you like
  -- but because `injective_def` is true by definition
  -- you can just skip this line
  rw injective_def,
  intros a b h,
  rw id_eval at h,
  rw id_eval at h,
  exact h,
end

example : surjective (id : X → X) :=
begin
  intro x,
  use x,
  refl,
end


#exit


example : x ∉ A → (x ∈ A → false) :=
begin
  sorry
end

example : x ∈ A → (x ∉ A → false) :=
begin
  sorry
end

example : (∀ t, t ∈ A → t ∈ B) → x ∉ B → x ∉ A :=
begin
  sorry
end

example : x ∉ (∅ : set X) :=
begin
  sorry
end
