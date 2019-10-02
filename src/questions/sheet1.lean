/-  Math40001 : Introduction to university mathematics.

Problem Sheet 1, October 2019.

Translated from pdf into Lean by Kevin Buzzard 
-/

-- We are doing classical logic.
local attribute [instance, priority 10] classical.prop_decidable

/-
Question 1. Let P and Q be Propositions (that is, true/false statements).
Prove that P ∧ Q → Q ∧ P. 
-/
lemma question_one (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  sorry
end
/-
For question 2, comment out one option and prove the other
-/

lemma question_2a_true : ∀ P Q : Prop, (P → Q) → (Q → P) :=
begin
  sorry
end

lemma question_2a_false : ¬ (∀ P Q : Prop, (P → Q) → (Q → P)) :=
begin
  sorry
end

lemma question_2b_true (P Q : Prop) : (P ↔ Q) → (Q ↔ P) :=
begin
  sorry
end

lemma question_2b_false : ¬ (∀ P Q : Prop, (P ↔ Q) → (Q ↔ P)) :=
begin
  sorry
end

lemma question_3_true (P Q R : Prop) 
  (h1 : Q → P)
  (h2 : ¬ Q → ¬ R) : 
R → P :=
begin
  sorry
end

lemma question_3_false : ¬ (∀ P Q R : Prop,  
  (Q → P) →
  (¬ Q → ¬ R) → 
  R → P) :=
begin
  sorry
end

/- In question 4 you must *change the conclusion* to explain
   what you deduced.
-/

**TODO**
lemma question_4 (P Q R : Prop) : P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R :=
begin
  split,
    intro h,
    cases h with hP hQR,
    cases hQR with hQ hR,
    split,
      split,
        assumption,
      assumption,
    assumption,
  intro h,
  cases h with hPQ hR,
  cases hPQ with hP hQ,
  split,
    assumption,
  split,
    assumption,
  assumption,    
end

/-
all of these questions can be solved using only the following
tactics:

intro
apply (or, better, refine)
left, right, cases, split
assumption (or, better, exact)
have,
simp
-/
