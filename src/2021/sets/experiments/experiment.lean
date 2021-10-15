import tactic

/-

## New tactics

`intro` for ∀
`specialize`
`tauto!`

 -/
variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : ∀ x : X, x ∈ A → x ∈ A :=
begin
  intro x,
  intro hx,
  exact hx,
end

example : ∀ x : X, (x ∈ A ∧ x ∈ B) → x ∈ A :=
begin
  intro x,
  intro h,
  cases h with h1 h2,
  exact h1,
end

example : (∀ x, x ∈ A ∧ x ∈ B) → (∀ x, x ∈ A) :=
begin
  intro h,
  intro x,
  specialize h x,
  cases h with hA hB,
  exact hA,
end

example : (∀ x, x ∈ A ∧ x ∈ B) → (∀ x, x ∈ B ∧ x ∈ A) :=
begin
  intro h,
  intro x,
  specialize h x,
  cases h with hA hB,
  split;
  assumption,
end

example : (∀ x, x ∉ A ∨ x ∈ B) → (∀ x, x ∈ A → x ∈ B) :=
begin
  intro h,
  intro x,
  specialize h x,
  tauto!,
end

/-

## new tactics

`cases` for `∃`
`use`

-/

example : (∃ x, x ∈ A) → ∃ x, x ∈ A ∨ x ∈ B :=
begin
  intro h,
  cases h with x hx,
  use x,
  tauto!,
end

example : (∃ x, x ∈ A ∧ x ∈ B) → (∃ x, x ∈ B ∧ x ∈ A) :=
begin
  sorry
end

-- need to know about ∉ 
example : (∃ x, x ∈ A) → ¬ (∀ x, x ∉ A) := -- can do ↔, can swap ∈ to ∉ 
begin
  intro h,
  cases h with x hxA,
  intro h,
  specialize h x,
  sorry
end  