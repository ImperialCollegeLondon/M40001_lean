/-  Math40001 : Introduction to university mathematics.

Problem Sheet 2, October 2020.

This is a Lean file. It can be read with the Lean theorem prover.

You can work on this file online via the link at
https://github.com/ImperialCollegeLondon/M40001_lean/blob/master/README.md


or you can install Lean and its maths library following the
instructions at
https://leanprover-community.github.io/get_started.html

and then just clone the project onto your own computer
with `leanproject get ImperialCollegeLondon/M40001_lean`.

There are advantages to installing Lean on your own computer
(for example it's faster), but it's more hassle than
just using it online.

In the below, delete "sorry" and replace it with some
tactics which prove the result.

-/

import data.real.basic -- need real numbers for Q5

-- Q1 prove that ∩ is symmetric
lemma question1 (α : Type) (X Y : set α) : X ∩ Y = Y ∩ X :=
begin
  sorry
end

-- question 2 defs
def A := {x : ℝ | x ^ 2 < 3}
def B := {x : ℝ | ∃ n : ℤ, x = n ∧ x ^ 2 < 3}
def C := {x : ℝ | x ^ 3 < 3}

-- Change _true to _false and put a ¬ in front
-- of the goal if you think it's false.
-- e.g. if you think 2c is false then don't
-- try to prove it's true, try proving
-- lemma question2c_false : ¬ (A ⊆ C) := ...

-- Some of these are tricky for Lean beginners.

lemma question2a_true : (1 : ℝ)/2 ∈ A ∩ B :=
begin
  sorry
end

lemma question2b_true : (1 : ℝ)/2 ∈ A ∪ B :=
begin
  sorry
end

lemma question2c_true : A ⊆ C :=
begin
  sorry
end

lemma question2d_true : B ⊆ C :=
begin
  sorry
end

lemma question2e_true : C ⊆ A ∪ B :=
begin
  sorry
end

lemma question2f_true : (A ∩ B) ∪ C = (A ∪ B) ∩ C :=
begin
  sorry
end

-- Q3 set-up
variables (X Y : Type)
variable (P : X → Prop)
variable (Q : X → Prop)
variable (R : X → Y → Prop)

-- for Q3 you're going to have to change the right hand
-- side of the ↔ in the statement
-- of the lemma to the answer you think is correct.

lemma question3a : ¬ (∀ x : X, P x ∧ ¬ Q x) ↔ true := -- change `true`!
begin
  sorry
end

lemma question3b : ¬ (∃ x : X, (¬ P x) ∧ Q x) ↔ true := -- change `true`!
begin
  sorry
end

lemma question3c : ¬ (∀ x : X, ∃ y : Y, R x y) ↔ true := -- change `true`!
begin
  sorry
end

example (f : ℝ → ℝ) (x : ℝ) :
  ¬ (∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ y : ℝ, abs (y - x) < δ → abs (f y -f x) < ε )
↔ -- change next line to what you think the answer is
true :=
begin
  sorry
end

-- change _true to _false in 4a, 4b if you think the opposite is true
-- and stick a `¬` in front of it
lemma question4a_true : ∀ x : ℝ, ∃ y : ℝ, x + y = 2 :=
begin
  sorry
end

lemma question4b_true : ∃ y : ℝ, ∀ x : ℝ, x + y = 2 :=
begin
  sorry
end 

-- similarly for Q5 -- change _true to _false and add in a negation if you 
-- want to prove that the proposition in the question is false.
lemma question5a_true : ∃ x ∈ (∅ : set ℕ), 2 + 2 = 5 :=
begin
  sorry
end

lemma question5b_true : ∀ x ∈ (∅ : set ℕ), 2 + 2 = 5 :=
begin
  sorry
end 
