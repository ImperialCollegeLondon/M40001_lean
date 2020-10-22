import tactic

variables (x y : ℕ)

open nat

theorem Q1a : x + y = y + x :=
begin
  induction y with d hd,
  { rw [add_zero, zero_add] },
  { rw [add_succ, succ_add, hd] }
end

theorem Q1b : x + y = x → y = 0 :=
begin
  intro h,
  induction x with d hd,
  { convert h, rw zero_add },
  { apply hd,
    rw succ_add at h,
    rw ← succ_inj',
    assumption,
  }
end

theorem Q1c : x + y = 0 → x = 0 ∧ y = 0 :=
begin
  intro h,
  induction y with d hd,
  { split,
    { exact h },
    { refl },
  },
  { rw add_succ at h,
    exfalso,
    apply succ_ne_zero (x + d),
    assumption },
end

theorem Q1d : x * y = y * x :=
begin
  induction y with d hd,
  { rw [mul_zero, zero_mul]},
  { rw [mul_succ, succ_mul, hd]},
end
