import tactic

variables (x y : ℕ)

open nat

theorem Q1a : x + y = y + x :=
begin
  sorry
end

theorem Q1b : x + y = x → y = 0 :=
begin
  sorry
end

theorem Q1c : x + y = 0 → x = 0 ∧ y = 0 :=
begin
  sorry
end

theorem Q1d : x * y = y * x :=
begin
  sorry
end

theorem Q2a : 1 * x = x ∧ x = x * 1 :=
begin
  sorry
end

variable z : ℕ

theorem Q2b : (x + y) * z = x * z + y * z :=
begin
  sorry
end

theorem Q2c : (x * y) * z = x * (y * z) :=
begin
  sorry
end


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





