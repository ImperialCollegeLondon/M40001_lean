import tactic

variables (x y : ℕ)

open nat

-- Q3 def
def is_pred (x y : ℕ) := x.succ = y

theorem Q3a : ¬ ∃ x : ℕ, is_pred x 0 :=
begin
  sorry
end

theorem Q3b : y ≠ 0 → ∃! x, is_pred x y :=
begin
  sorry
end

def aux : 0 < y → ∃ x, is_pred x y :=
begin
  sorry
end

-- definition of pred' is "choose a random d such that succ(d) = n"
noncomputable def pred' : ℕ+ → ℕ := λ nhn, classical.some (aux nhn nhn.2)

theorem pred'_def : ∀ np : ℕ+, is_pred (pred' np) np :=
λ nhn, classical.some_spec (aux nhn nhn.2)

def succ' : ℕ → ℕ+ :=
λ n, ⟨n.succ, zero_lt_succ n⟩

noncomputable definition Q3c : ℕ+ ≃ ℕ :=
{ to_fun := pred',
  inv_fun := succ',
  left_inv := begin
    sorry
  end,
  right_inv := begin
    sorry
  end
   }

