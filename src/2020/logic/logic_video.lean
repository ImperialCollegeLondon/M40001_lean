import tactic

-- Definition: a Proposition is a type `P`, where `P : Prop`.

variables (P Q R : Prop)

-- In Lean, `P → Q` means `P ⇒ Q`

example : P → P :=
begin
  intro hP, -- let hP be the hypothesis that P is true
  exact hP, -- our goal is exactly our hypothesis
end

example : P → (Q → P) :=
begin
  intro hP, -- let hP be the hypothesis that P is true
  intro hQ,
  exact hP,
end

-- is → associative? i.e. Does (P → Q) → R equal P → (Q → R) ?
-- (A+B)+C = A+(B+C)  
-- (A-B)-C ≠ A-(B-C)
-- (A-B)-C 
-- 2^(1^3) -- this is the convention for powers

-- CONVENTION: P → Q → R with no brackets MEANS P → (Q → R)

example : P → Q → P :=
begin
  intro hP,
  intro hQ,
  exact hP,
end

/-- Modus Ponens : if P is true, and P → Q, then Q is true -/
theorem modus_ponens : P → (P → Q) → Q :=
begin
  intro hP,
  intro hPQ, -- hPQ is the hypothesis that P → Q
  apply hPQ, -- apply the hypothesis that P → Q
  exact hP,
end

-- If `a<b` and `b<c` then `a<c` -- that's called "transitivity of <"

-- theorem transitivity : (P → Q) → (Q → R) → (P → R) :=
-- begin
--   sorry
-- end

example : (P → Q → R) → (P → Q) → (P → R) :=
begin
  intro hPQR,
  intro hPQ,
  intro hP,
  apply hPQR,
    assumption,
  apply hPQ,
  assumption,
end

-- in Lean, the definition of ¬ P is `P → false` 
-- if P is true, ¬ P is false, and P → false is false
-- if P is false, then ¬ P is true, and P → false is true

example : P → ¬ (¬ P) :=
begin
  intro hP,
  change (¬ P → false),
  intro hnP,
  change P → false at hnP,
  apply hnP,
  assumption,
end

example : ¬ (¬ P) → P :=
begin
  finish,
end

example : P → ¬ (¬ P) :=
begin
  apply modus_ponens,
end

-- and

example : P ∧ Q → P :=
begin
  intro hPaQ,
  cases hPaQ with hP hQ,
  assumption,
end

theorem and.elim' : P ∧ Q → (P → Q → R) → R :=
begin
  intro hPaQ,
  intro hPQR,
  cases hPaQ with hP hQ,
  apply hPQR;
  assumption,
end

theorem and.intro' : P → Q → P ∧ Q :=
begin
  intro hP,
  intro hQ,
  split,
    assumption,
  assumption,
end





