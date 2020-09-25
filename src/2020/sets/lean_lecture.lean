import tactic 

import data.real.basic

example : ∀ x : ℝ, ∃ y : ℝ, x + y ≥ 0 :=
begin
  intro x,
  use 37 - x,
  simp,
  norm_num,
end

-- example : ∃ y : ℝ, ∀ x : ℝ, x + y ≥ 0 :=
-- begin
--   use 100000000000000000000,
--   intro x,
--   -- this is impossible
--   sorry
-- end

example : ¬ (∃ y : ℝ, ∀ x : ℝ, x + y ≥ 0) :=
begin
  push_neg,
  intro y,
  use -37-y,
  simp,
  norm_num,
end

-- construction 1 and construction 2
-- showed that predicates on α corresponded to subsets of α

variable (α : Type)

example : (α → Prop) ≃ set α :=
{ to_fun := λ P, {x : α | P x},
  inv_fun := λ X, λ a, a ∈ X,
  left_inv := begin
    intro P,
    dsimp,
    refl,
  end,
  right_inv := begin
    intro X,
    dsimp,
    refl,
  end }