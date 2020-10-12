import tactic

-- Let X be the set {A,B,C}
inductive X
| A : X
| B : X
| C : X

open X

def R (x y : X) : Prop := (x = A ∧ y = B) ∨ (x = A ∧ y = C)
-- R(A,B) and R(A,C) both true, everything else false

theorem R_fst {x y : X} : R x y → x = A :=
begin
  intro h,
  cases h,
    cases h,
    assumption,
  cases h,
  assumption,
end

example : transitive R :=
begin
  intros x y z,
  intro hxy,
  intro hyz,
  have h1 := R_fst hxy,
  have h2 := R_fst hyz,
  subst h1,
  subst h2,
  assumption,
end

example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro hPQ,
  intro hnQ,
  intro hP,
  apply hnQ,
  exact hPQ hP,
end

