/-
What I present in M40001 is in some sense the mathematics
of true-false statements.
-/
import tactic

open bool

/-
#print notation ∧
#print and
-- This is one idea of a proposition.
-- ff and tt are the only two terms of type `bool`
-- functions band, bor, bnot
#check ff ∧ tt
#eval band ff tt 
#eval tt
-/
example : ∀ p q r : bool,
  p && (q || r) = (p && q) || (p && r)
:=
begin
  intros,
  cases p;
  cases q;
  cases r;
  refl
end

-- make some pdf notes with URLs
example : ∀ p q r : bool,
  p && (q || r) = (p && q) || (p && r)
:=
begin
  intros,
  cases p;
  cases q;
  cases r;
  refl
end

/-
Very boring proofs.

But there is always something very weird about
the definition of →. Should it really be the case
that we say "p implies q" if p is completely
irrelevant to the proof of q? 
But there is actually a much more profound definition
of a Proposition. A Proposition in Lean is a type `P`, 
where `P : Prop`. 

You can make pretty much all of the material in
the pure part of Imperial's undergraduate degree
in Lean now, because of its maths library `mathlib`.
Many Imperial students have contributed to 
mathlib, but it's now getting harder for beginners
to help out.  


This definition looks intimidating
but it is not. A term `p : P` (that is,
a term `p` of type `P`)
is a proof of `P`. In this model of the idea of a
proposition, implication `P ⇒ Q` is a function,
which takes as input a proof of `P` and outputs a
proof of `Q`. In other words, a function
which takes as input a term of type `P` and outputs
a term of type `Q`. In other words, it's
a function `P → Q` between the types `P` and `Q`.

Important thing: any two proofs of `P` are equal.
If `p : P` and `q : P` then `p = q`. This model
of the word "proposition" cannot distinguish
between proofs. Internally a proof knows how
much work it was to construct though.
-/

/-
Let's do some constructive logic.
Let's play with the idea of `P → Q`.
-/

namespace xena

variables (P Q R : Prop)

/-- The theorem that P ⇒ P -/
theorem id : P → P :=
begin
  -- `⊢ X` on the right means "you've got to prove X"
  -- so we've got to prove P → P
  -- assume that `P` is true. 
  -- call this hypotheis `hP`
  intro hP,
  -- now we've got to prove `P`
  exact hP,
  -- we never mentioned `P`
  -- we just talked about hypotheses
end

example : P → (Q → P) :=
begin
  intro hP,
  intro hQ,
  exact hP
end
-- then remove bracket at the top

example : P → (P → Q) → Q :=
begin
  intro hP,
  intro hPQ,
  apply hPQ, clear hPQ,
  exact hP,
end

example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  intro hPQR,
  intro hPQ,
  intro hP,
  apply hPQR,
    exact hP,
  exact hPQ(hP),
end
-- todo -- search for why I don't get multicoloured tada

example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  cc,-- "congruence closure"
end



end xena

