/-  MATH40001 : Introduction to university mathematics.

Peano Axioms - Extra Practice, October 2020.

These questions are based on Dr Lawn's Practice Questions
on Blackboard.

This is a Lean file. It can be read with the Lean theorem prover.

You can work on this file online at the following URL:


or you can install Lean and its maths library following the instructions at
https://leanprover-community.github.io/get_started.html

There are advantages to installing Lean on your own computer
(for example it's faster), but it's more hassle than just using it online.


Replace the sorries for the theorems you think are provable
with tactics which prove them.

Here, we use the function `succ` instead of `ν`.
-/

import data.nat.basic

open nat function

#check (succ : ℕ → ℕ)
#reduce succ 0
#reduce succ 36


theorem exists_succ_true : ∃ (ν : ℕ → ℕ), ν = succ :=
begin
  sorry
end

theorem exists_succ_false : ¬ ∃ (ν : ℕ → ℕ), ν = succ :=
begin
  sorry
end


theorem succ_injective_true : injective succ :=
begin
  unfold injective,
  sorry
end

theorem succ_injective_false : ¬ injective succ :=
begin
  unfold injective,
  sorry
end


theorem succ_surjective_true : surjective succ :=
begin
  unfold surjective,
  sorry
end

theorem succ_surjective_false : ¬ surjective succ :=
begin
  unfold surjective,
  sorry
end


theorem all_functions_are_succ_true : ∀ (ν : ℕ → ℕ), ν = succ :=
begin
  sorry
end

theorem all_functions_are_succ_false : ¬ ∀ (ν : ℕ → ℕ), ν = succ :=
begin
  sorry
end


theorem exists_unique_zero_true : ∃! n : ℕ, n = 0 :=
begin
  sorry
end

theorem exists_unique_zero_false : ¬ ∃! n : ℕ, n = 0:=
begin
  sorry
end

/-
The lemma
`funext_iff` : (f₁ = f₂) ↔ (∀ x, f₁ x = f₂ x)
might come in handy somewhere above.

Next, try writing down the Peano Axioms as given in the lectures/notes:

type `\forall`, `\exists`, `\nu`, `\in`, `\sub` and `\to`
and then SPACE or TAB for their respective symbols ∀ ∃ ν ∈ ⊆ →
-/

def N : set ℕ := {n | true} -- Let `N` be the set of all natural numbers

def Peano_Axiom_1 : Prop := 0 ∈ N -- as an example
def Peano_Axiom_2 : Prop := sorry
def Peano_Axiom_3 : Prop := sorry
def Peano_Axiom_4 : Prop := sorry
def Peano_Axiom_5 : Prop := sorry



-- Lean Fun Facts!

set_option pp.numerals false  -- changes lean's pretty printer options

#reduce succ 5
#reduce 37

#check 6
#check 37

-- Compare Lean's recursor with (P5)
#check (@nat.rec : ∀ {C : ℕ → Sort*}, C 0 → (∀ n, C n → C (succ n)) → ∀ n, C n)
