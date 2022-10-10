/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-

# More on functions

Another question on the IUM problem sheet on functions
is "If `f : X → Y` and `g : Y → Z` and `g ∘ f` is injective, is it true that `g` is injective?"
This is not true. A counterexample could be made by letting `X` and `Z` have one element, 
and letting `Y` have two elements; `f` and `g` are then not hard to write down. Let's
see how to do this in Lean by making inductive types `X`, `Y` and `Z` and functions
`f` and `g` which give an explicit counterexample.

-/

-- Let X be {a}
inductive X : Type
| a : X

-- in fact the term of type X is called `X.a`.

-- Let Y be {b,c}
inductive Y : Type
| b : Y
| c : Y

inductive Z : Type
| d : Z

-- Define f by f(X.a)=Y.b
def f : X → Y
| X.a := Y.b

-- define g by g(Y.b)=g(Y.c)=Z.d
def g : Y → Z
| Y.b := Z.d
| Y.c := Z.d

-- examples of how these things work
example (z : Z) : z = Z.d :=
begin
  cases z,
  refl,
end

example : Y.b ≠ Y.c :=
begin
  intro h, -- x ≠ y is definitionally equal to (x = y) → false
  cases h, -- no cases when they're equal!
end


open function

lemma gf_injective : injective (g ∘ f) :=
begin
  sorry,
end

-- This is a question on the IUM function problem sheet
example : ¬ (∀ X Y Z : Type, ∀ (f : X → Y) (g : Y → Z), injective (g ∘ f) → injective g) :=
begin
  sorry,
end

-- This is another one
example : ¬ (∀ X Y Z : Type, ∀ (f : X → Y) (g : Y → Z), surjective (g ∘ f) → surjective f) :=
begin
  sorry,
end