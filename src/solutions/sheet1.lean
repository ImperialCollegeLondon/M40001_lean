/-  Math40001 : Introduction to university mathematics.

Problem Sheet 1, October 2019.

Translated from pdf into Lean by Kevin Buzzard 
-/

-- We are doing classical logic.
local attribute [instance, priority 10] classical.prop_decidable

/-
Question 1. Let P and Q be Propositions (that is, true/false statements).
In lectures we proved that P ∨ Q → Q ∨ P. Prove that P ∧ Q → Q ∧ P. 
-/
lemma question_one (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  by_cases h1 : P,
  by_cases h2 : Q,
  intros, split, assumption,assumption,
  intro h, cases h with hP hQ, exfalso, apply h2, exact hQ,
  intro h, cases h with hP hQ, exfalso, apply h1, exact hP,
end

lemma question_one' (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
  split,
    assumption,
  assumption,
end

lemma question_two : ¬ (∀ P Q : Prop, (P → Q) → (Q → P)) :=
begin
  intro h,
  have h2 := h false true,
  simp at h2,
  exact h2,
end

lemma question_1c (P Q : Prop) : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  cases h with h1 h2,
  split,
    assumption,
  assumption,
end

lemma question_1c' (P Q : Prop) : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  by_cases h1 : P,
    by_cases h2 : Q,
    split,
    intro _,
    assumption,
    intro _,
    assumption,
    exfalso,
    apply h2,
    rw ←h,
    assumption,
  by_cases h2 : Q,
    exfalso,
    apply h1,
    rw h,
    assumption,
  split,
    intro hQ, contradiction,
    intro hP, contradiction,
end

lemma question_1c'' (P Q : Prop) : (P ↔ Q) → (Q ↔ P) :=
λ ⟨hP, hQ⟩, ⟨hQ, hP⟩

lemma question_2 (P Q R : Prop) : P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R :=
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
