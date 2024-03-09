/-  Math40001 : Introduction to university mathematics.

Problem Sheet 4, October 2019.

This is a Lean file. It can be read with the Lean theorem prover.

You can work on this file online at 
https://tinyurl.com/Lean-M40001-Example-Sheet-4

or you can install Lean and its maths library following the
instructions at
https://github.com/leanprover-community/mathlib#installation

There are advantages to installing Lean on your own computer
(for example it's faster), but it's more hassle than
just using it online. 

In the below, delete "sorry" and replace it with some
tactics which prove the result.

-/

import data.real.basic -- the real numbers

namespace questions2019sheet4

/- Question 1. 

For each of the sets~$X$ and binary relations~$R$ below, figure out whether~$R$ is (a) reflexive, (b) symmetric, (c) antisymmetric, (d) transitive. 
  
  \begin{enumerate}
  \item Let $X$ be the set $\{1,2\}$ and define~$R$ like this: $R(1,1)$ is true, $R(1,2)$ is true, $R(2,1)$ is true and $R(2,2)$ is false. 
  \item Let~$X=\R$ and define $R(a,b)$ to be the proposition $a=-b$.
  \item Let~$X=\R$ and define $R(a,b)$ to be false for all real numbers~$a$ and~$b$.
  \item Let~$X$ be the empty set and define~$R$ to be the empty binary relation (we don't have to say what its value is on any pair $(a,b)$ because no such pairs exist).
  \end{enumerate}

-/

namespace Q1a

inductive X : Type
| one : X
| two : X

namespace X

def R : X → X → Prop
| one one := true
| one two := true
| two one := true
| two two := false

-- insert "¬" if you think it's not reflexive
lemma Q1a_refl : reflexive R := 
begin
  sorry
end

-- insert "¬" if you think it's not symmetric
lemma Q1a_symm : symmetric R := 
begin
  sorry
end

-- insert "¬" if you think it's not transitive
lemma Q1a_trans : transitive R := 
begin
  sorry
end

-- insert "¬" if you think it's not an equiv reln
lemma Q1a_equiv : equivalence R := 
begin
  sorry
end

end X
end Q1a

namespace Q1b

def R (a b : ℝ) : Prop := a = -b

-- insert "¬" if you think it's not reflexive
lemma Q1b_refl : reflexive R := 
begin
  sorry
end

-- insert "¬" if you think it's not symmetric
lemma Q1b_symm : symmetric R := 
begin
  sorry
end

-- insert "¬" if you think it's not transitive
lemma Q1b_trans : transitive R := 
begin
  sorry
end

-- insert "¬" if you think it's not an equiv reln
lemma Q1b_equiv : equivalence R := 
begin
  sorry
end

end Q1b

namespace Q1c

def R (a b : ℝ) : Prop := false

-- insert "¬" if you think it's not reflexive
lemma Q1c_refl : reflexive R := 
begin
  sorry
end

-- insert "¬" if you think it's not symmetric
lemma Q1c_symm : symmetric R := 
begin
  sorry
end

-- insert "¬" if you think it's not transitive
lemma Q1c_trans : transitive R := 
begin
  sorry
end

-- insert "¬" if you think it's not an equiv reln
lemma Q1c_equiv : equivalence R := 
begin
  sorry
end

end Q1c

namespace Q1d

def R (a b : empty) : Prop := by cases a -- i.e. "I'll define it in all cases -- oh look there are no cases"

-- insert "¬" if you think it's not reflexive
lemma Q1d_refl : reflexive R := 
begin
  sorry
end

-- insert "¬" if you think it's not symmetric
lemma Q1d_symm : symmetric R := 
begin
  sorry
end

-- insert "¬" if you think it's not transitive
lemma Q1d_trans : transitive R := 
begin
  sorry
end

-- insert "¬" if you think it's not an equiv reln
lemma Q1d_equiv : equivalence R := 
begin
  sorry
end

end Q1d

-- `set ℤ` is the type of subsets of the integers.

def Q2a : partial_order (set ℤ) :=
{ le := λ A B, A ⊆ B,
  le_refl := begin sorry end,
  le_antisymm := begin sorry end,
  le_trans := begin sorry end
   }

-- insert ¬ at the beginning if you think it's wrong
lemma Q2b : is_total (set ℤ) (λ A B, A ⊆ B) :=
begin
  sorry
end

-- put ¬ in front if you think it's wrong
lemma Q3a : symmetric (λ a b : ℝ, a < b) :=
begin
  sorry
end

-- put ¬ in front if you think it's wrong
lemma Q3b : symmetric (λ a b : (∅ : set ℝ), a < b) :=
begin
  sorry
end

-- type in the proof in the question. Where do you get stuck?
lemma Q4 (X : Type) (R : X → (X → Prop)) (hs : symmetric R) (ht : transitive R) : reflexive R :=
begin
  sorry
end 

open function

definition pals {X Y Z : Type} (f : X → Y) (g : X → Z) := ∃ h : Y → Z, bijective h ∧ g = h ∘ f

lemma Q5 (X Y Z: Type) (f : X → Y) (g : X → Z) (hf : surjective f) (hg : surjective g) : pals f g ↔ ∀ a b : X, (f a = f b) ↔ (g a = g b) :=
begin
  sorry
end

end questions2019sheet4
