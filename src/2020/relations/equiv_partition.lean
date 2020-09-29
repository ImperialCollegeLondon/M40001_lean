import tactic

import data.setoid.partition

--#check setoid.partition.rel_iso

open setoid

variable (α : Type)

-- mathlib has this function already.
/-
def classes (r : setoid α) : set (set α) :=
{s | ∃ y, s = {x | r.rel x y}}
-/

example : {p : set (set α) // is_partition p} ≃
  setoid α :=
{ to_fun := λ pa, { r := λ (a b : α), ∀ X ∈ pa.1, a ∈ X → b ∈ X,
  iseqv :=
  begin
    sorry  
  end },
  inv_fun := λ r, ⟨classes r,
  begin
    sorry 
  end⟩,
  left_inv := begin
    sorry
  end,
  right_inv := begin
    sorry
  end }


