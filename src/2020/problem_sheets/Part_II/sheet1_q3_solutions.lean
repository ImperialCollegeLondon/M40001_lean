import tactic

variables (x y : ℕ)

open nat

theorem Q1a : x + y = y + x :=
begin
  induction y with d hd,
  { rw [add_zero, zero_add]},
  { rw [add_succ, succ_add, hd]}
end

theorem Q1b : x + y = x → y = 0 :=
begin
  intro h,
  induction x with d hd,
  { convert h, rw zero_add},
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
      exact h,
    refl,
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

theorem Q2a : 1 * x = x ∧ x = x * 1 :=
begin
  split,
  { induction x with d hd,
      refl,
    rw [mul_succ,hd],
  },
  rw [mul_succ, mul_zero, zero_add],
end

variable z : ℕ

theorem Q2b : (x + y) * z = x * z + y * z :=
begin
  induction z with d hd,
    refl,
  rw [mul_succ, hd, mul_succ, mul_succ],
  ac_refl,
end

theorem Q2c : (x * y) * z = x * (y * z) :=
begin
  induction z with d hd,
  { refl },
  { rw [mul_succ, mul_succ, hd, mul_add] }
end

-- Q3 def
def is_pred (x y : ℕ) := x.succ = y

theorem Q3a : ¬ ∃ x : ℕ, is_pred x 0 :=
begin
  intro h,
  cases h with x hx,
  unfold is_pred at hx,
  apply succ_ne_zero x,
  assumption,
end

theorem Q3b : y ≠ 0 → ∃! x, is_pred x y :=
begin
  intro hy,
  cases y,
    exfalso,
    apply hy,
    refl,
  clear hy,
  use y,
  split,
  { dsimp only,
    unfold is_pred,
  },
  intro z,
  dsimp only [is_pred],
  exact succ_inj'.1,
end

def aux : 0 < y → ∃ x, is_pred x y :=
begin
  intro hy,
  cases Q3b _ (ne_of_lt hy).symm with x hx,
  use x,
  exact hx.1,
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
    rintro np,
    have h := pred'_def,
    unfold succ',
    ext, dsimp,
    unfold is_pred at h,
    rw h,
  end,
  right_inv := begin
    intro n,
    unfold succ',
    have h := pred'_def,
    unfold is_pred at h,
    rw ← succ_inj',
    rw h,
    clear h,
    refl,
  end
   }

