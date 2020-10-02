import tactic

-- Let's make bijections between ℕ, ℤ and ℚ.

#check infinite

#print prefix infinite
#print infinite

#print int.infinite
#check infinite.of_injective

example : infinite ℕ := by apply_instance
example : infinite ℤ := by show_term {apply_instance}

#check rat.of_int

example : infinite ℚ := infinite.of_injective (coe : ℤ → ℚ)
begin
  intros a b,
  intro h,
  exact (rat.coe_int_inj a b).mp h,
end

namespace countably_infinite

example (a b : ℕ) : 2 * a = 2 * b → a = b := by 
begin
  intro h,
  apply mul_left_cancel' _ h,
  norm_num,
end

def bool_times_nat : bool × ℕ ≃ ℕ :=
{ to_fun := λ bn, if bn.1 = tt then bn.2 * 2 else bn.2 * 2 + 1,
  inv_fun := λ d, ⟨d % 2 = 0, d / 2⟩,
  left_inv := begin
    intro bn,
    cases bn with b n,  
    cases b,
    -- TODO -- make snippet
    { suffices : ¬(1 + 2 * n) % 2 = 0 ∧ (1 + 2 * n) / 2 = n,
      simpa [mul_comm, add_comm],
      have h : (1 + 2 * n) % 2 = 1,
        simp,
      split,
      { simp },
      { have h2 := nat.mod_add_div (1 + 2 * n) 2,
        have h3 : 2 * ((1 + 2 * n) / 2) = 2 * n →
          (1 + 2 * n) / 2 = n := λ h, mul_left_cancel' _ h,
        simp * at *, cc } },
    { simp }
  end
  ,
  right_inv := begin
    intro n,
    suffices : ite (n % 2 = 0) (n / 2 * 2) (n / 2 * 2 + 1) = n,
      simpa,
    split_ifs,  
  end
   }



example (X : Type) (h : X ≃ ℕ) : X ≃ X × bool := sorry

end countably_infinite

