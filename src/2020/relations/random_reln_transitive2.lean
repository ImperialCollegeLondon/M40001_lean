import tactic

-- Let X be the set {A,B,C}
inductive X
| A : X
| B : X
| C : X

open X

def R (x y : X) : Prop := (x = A ∧ y = B) ∨ (x = A ∧ y = C)

theorem R_fst {x y : X} : R x y → x = A :=
begin
  sorry
end

example : transitive R :=
begin
  sorry
end

example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry
end


