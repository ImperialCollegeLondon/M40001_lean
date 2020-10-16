import tactic

/-!

# Tactic cheat sheet. 



apply, rw, use, intro, rw at \|- h, exact, assumption, split

convert
ext
have
They need `use` to kill` nonempty X`

rintros, have, specialize,

-/

/-!

## 1) Extracting information from hypotheses

-/

/-! 

### 1a) cases and rcases

Many objects in Lean are pairs of data. For example, a proof
of `P ∧ Q` is stored as a pair consisting of a proof of `P` and
a proof of `Q`. The hypothesis `∃ n : ℕ, f n = 37` is stored
internally as a pair, namely a natural `n` and a proof that `f n = 37`.
Note that "hypothesis" and "proof" mean the same thing.

If `h : X` is something which is stored as a pair in Lean,
then `cases h with a b` will destroy `h` and replace it with
the two pieces of data which made up `h`, calling them `a` and `b`.

-/

example (h : ∃ n : ℕ, n ^ 2 = 2) : false :=
begin
  -- h: ∃ (n : ℕ), n ^ 2 = 2
  cases h with n hn,
  -- n: ℕ
  -- hn: n ^ 2 = 2
  sorry
end

example (P Q : Prop) (h : P ∧ Q) : P :=
begin
  -- h: P ∧ Q
  cases h with hP hQ,
  -- hP: P
  -- hQ: Q
  exact hP,
end

-- Some things are more than two pieces of data! You can do much more
-- elaborate deconstructions with the `rcases` command.

example (R : ℕ → ℕ → Prop) (hR : equivalence R) : symmetric R :=
begin
  -- hR: equivalence R
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  -- hrefl: reflexive R
  -- hsymm: symmetric R
  -- htrans: transitive R
  exact hsymm,
end

/-!

## 1b) specialize

Say you have a long hypothesis `h : ∀ n : ℕ, f n > 37 → n = 23`.
This hypothesis is a *function*. It takes as inputs a natural number n
and a proof that `f n > 37`, and then it gives as output a proof
that `n = 23`. You can feed in some inputs and specialize the function.

Say for example you you manage to prove the hypothesis `ht : f t > 37` for some natural
number `t`. Then `specialize h t ft` would change `h` to `t = 23`.

-/

example (X Y : set ℕ) (a : ℕ) (h : ∀ n : ℕ, n ∈ X → n ∈ Y) (haX : a ∈ X) : a ∈ Y :=
begin
  -- a: ℕ
  -- haX: a ∈ X
  -- h: ∀ (n : ℕ), n ∈ X → n ∈ Y
  specialize h a haX,
  -- h: a ∈ Y
  assumption,
end

/-!

# 2) Making new hypothesis

-/

/-!

## have

The `have` tactic makes a new hypothesis. The proof of the current goal
is paused and a new goal is created. Generally one should now put braces
`{ }` because if there is more than one goal then understanding what the
code is doing can get very difficult.

-/

example (a b c n : ℕ) (hn : n > 2) : a^n + b^n = c^n → a * b = 0 :=
begin
  -- ⊢ a ^ n + b ^ n = c ^ n → a * b = 0
  -- looks a bit tricky
  -- why not prove something easier first
  have ha : (a + 1) + 1 = a + 2,
  { -- ⊢ a + 1 + 1 = a + 2
    apply add_assoc,
  },
  -- ha: a + 1 + 1 = a + 2
  -- ⊢ a ^ n + b ^ n = c ^ n → a * b = 0
  sorry
end

/-!

# 2) Using hypotheses on the goal.

-/

/-!

## 2a) rw

The generic `sub in` tactic. If `h : X = Y` then `rw h` will change all
`X`'s in the goal to `Y`'s. Also works with `h : P ↔ Q` if `P` and `Q`
are true-false statements. 

-/

example (X Y : set ℕ) (hXY : X = Y) (a : ℕ) (haX : a ∈ Y) : a ∈ X :=
begin
  -- hXY: X = Y
  -- ⊢ a ∈ X
  rw hXY,
  -- hXY: X = Y
  -- ⊢ a ∈ Y
  assumption
end

/-

Variants -- `rw h1 at h2`, `rw h1 at h2 ⊢`, `rw h at *`
-/


/-

# Changing the goal

-/

/-! ### intro and rintro -/

-- `intro` is a basic tactic for introducing hypotheses
example (P Q : Prop) : P → Q :=
begin
  -- ⊢ P → Q
  intro hP,
  -- hP: P
  -- ⊢ Q
  sorry
end

-- `rintro` is to `intro` what `rcases` is to `cases`. It enables
-- you to assume something and simultaneously take it apart.

example (f : ℕ → ℚ) : (∃ n : ℕ, f n > 37) → (∃ n : ℕ, f n > 36) :=
begin
  -- ⊢ (∃ (n : ℕ), f n > 37) → P
  rintro ⟨n, hn⟩,
  --  n: ℕ
  -- hn: f n > 37
  -- ⊢ P
end
