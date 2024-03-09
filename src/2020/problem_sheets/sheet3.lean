/-  Math40001 : Introduction to university mathematics.

Problem Sheet 3, October 2020.

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

import data.real.basic -- the real numbers

namespace problem_sheets_2020_sheet_3

/- Question 1. 

  Say $X$, $Y$ and $Z$ are sets, and $f:X\to Y$ and $g:Y\to Z$ are functions. In lectures we proved that if 
$f$ and $g$ are injective, then $g\circ f$ is also injective, and we will prove on Monday that if $f$ and $g
$ are surjective, then $g\circ f$ is surjective. But what about the other way?
  \begin{enumerate}
  \item If $g\circ f$ is injective, then is $f$ injective? Give a proof or a counterexample.
  \item If $g\circ f$ is injective, then is $g$ injective? Give a proof or a counterexample.
  \item If $g\circ f$ is surjective, then is $f$ surjective? Give a proof or a counterexample.
  \item If $g\circ f$ is surjective, then is $g$ surjective? Give a proof or a counterexample.
  \end{enumerate}
-/

open function 

-- in Q1 you would be best off defining the counterexample explicitly before you embark upon the
-- disproofs of the false statements

-- put ¬ in front of the ∀ and put everything in brackets if you want to disprove it
lemma question_one_a_true : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), injective (g ∘ f) → injective f :=
begin
  sorry
end

-- put ¬ in front of the ∀ and put everything in brackets if you want to disprove it
lemma question_one_b_true : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), injective (g ∘ f) → injective g :=
begin
  sorry
end

-- put ¬ in front of the ∀ and put everything in brackets if you want to disprove it
lemma question_one_c_true : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), surjective (g ∘ f) → surjective f :=
begin
  sorry
end

-- put ¬ in front of the ∀ and put everything in brackets if you want to disprove it
lemma question_one_d_true : ∀ (X Y Z : Type) (f : X → Y) (g : Y → Z), surjective (g ∘ f) → surjective g :=
begin
  sorry
end

/-
% Q2
\item For each of the following functions, decide whether or not they are injective, surjective, bijective. 
Proofs required!

  \begin{enumerate}
    \item $f:\R\to\R$, $f(x)=1/x$ if $x\not=0$ and $f(0)=0$.
\item  $f : \R\to\R$, $f(x)=2x+1$.
\item  $f:\Z\to\Z$, $f(x)=2x+1$.
\item  $f:\R\to\R$ defined by $f(x)=3-x$ if the Riemann hypothesis is true, and $f(x)=2+x$ if not. [NB the \
href{https://en.wikipedia.org/wiki/Riemann_hypothesis}{Riemann Hypothesis} is a hard unsolved problem in mat
hematics; nobody currently knows if it is true or false.]
\item $f:\Z\to\Z$, $f(n)=n^3-2n^2+2n-1$.
\end{enumerate}

-/

-- this line just says "we're mathematicians so every proposition is either true or false"
open_locale classical

-- this line says "a function might not be defined by an algorithm"
noncomputable theory 

-- definition of the functions in Q2."λ x," is the way computer scientists say "x ↦"

def fa : ℝ → ℝ := λ x, 1 / x -- Lean defines 1/0 to be 0

def fb : ℝ → ℝ := λ x, 2 * x + 1

def fc : ℤ → ℤ := λ x, 2 * x + 1

constant Riemann_Hypothesis : Prop -- doesn't matter what it says

def fd : ℝ → ℝ := λ x, if Riemann_Hypothesis then 3 - x else 2 + x

def fe : ℤ → ℤ := λ n, n ^ 3 - 2 * n ^ 2 + 2 * n - 1

-- now write your own questions, below are some examples (that may or may not be possible to prove)
lemma Q2a1 : injective fa := sorry
lemma Q2a2 : ¬ (surjective fa) := sorry 
lemma Q2c3 : bijective fc := sorry 

/-
Question 3 is "why does this not make sense" so it can't be formalised.
-/

/-
  % Q4
\item  Prove the claim I will make in lecture on Monday, saying that if $f:X\to Y$ is a function, and $g:Y\t
o X$ is a two-sided inverse of~$f$, then~$f$ is a two-sided inverse for~$g$. Deduce that if~$X$ and~$Y$ are 
sets, and there exists a bijection from~$X$ to~$Y$, then there exists a bijection from~$Y$ to~$X$.
-/

lemma Q4a (X Y : Type) (f : X → Y) (g : Y → X) (h2sided : (∀ x : X, g (f x) = x) ∧ (∀ y : Y, f (g y) = y)) : 
(∀ y : Y, f (g y) = y) ∧ (∀ x : X, g (f x) = x) := sorry

-- you will need this result to do the second part. Ignore the proof, I'm using term mode just to
-- make it quicker. Note that this crazy-looking proof is an indication that there are other
-- ways of using Lean apart from tactic mode.

lemma exists_bijection_iff_has_two_sided_inverse (X Y : Type) :
(∃ f : X → Y, bijective f) ↔ (∃ (f : X → Y), ∃ (g : Y → X), (∀ x : X, g (f x) = x) ∧ (∀ y : Y, f (g y) = y)) :=
⟨λ ⟨f, hf⟩, ⟨f, bijective_iff_has_inverse.1 hf⟩,
 λ ⟨f, g, hgf, hfg⟩, ⟨f, bijective_iff_has_inverse.2 ⟨g, hgf, hfg⟩⟩⟩

lemma Q4b (X Y : Type) : (∃ f : X → Y, bijective f) ↔ (∃ g : Y → X, bijective g) := sorry

/-
  % Q5
  \item Let~$Z$ be a set. If $f:X\to Z$ and $g:Y\to Z$ are injective functions, let's say that $f$ \emph{is 
friends with} $g$ if there is a bijection $h:X\to Y$ such that $f=g\circ h$. Prove that $f$ is friends with 
$g$ if and only if the image of~$f$ equals the image of~$g$. NB: by the \emph{image} of $f:X\to Z$ I mean th
e subset of~$Z$ consisting of things ``hit'' by $f$, in other words the set $\{z\in Z\,:\,\exists x\in X, f(
x)=z\}$. Some people call this the ``range'' of $f$, although other people use ``range'' to mean the same th
ing as ``codomain'' :-| 

-/

def friends {X Y Z : Type} (f : X → Z) (g : Y → Z) (hf : injective f) (hg : injective g) :=
  ∃ h : X → Y, bijective h ∧ f = g ∘ h

lemma Q5 (X Y Z : Type) (f : X → Z) (g : Y → Z) (hf : injective f) (hg : injective g) :
friends f g hf hg ↔ set.range f = set.range g := sorry

end problem_sheets_2020_sheet_3
