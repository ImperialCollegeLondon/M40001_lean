import tactic

open_locale classical

open set

example (f : ℕ → ℕ) : f = id ↔ ∀ n, f (f n) < f (n + 1) :=
begin
  split,
  { -- easy way
    rintro rfl,
    -- it's obvious
    simp },
  { -- interesting way
    -- Assume `f(f(n))<f(n+1)` for all n
    intro hf,
    -- Let S be the range of f
    set S := range f with hS,
    -- Then S is nonempty
    have h : ∃ d, d ∈ S,
      use f(37),
      simp,
    -- let m be the minimal element
    set m := nat.find h with hm1,
    -- Of course m is in S
    have hm2 : m ∈ S,
      apply nat.find_spec h,
    -- and it's smaller than the other elements
    have hm3 : ∀ x ∈ S, m ≤ x,
      intro x,
      exact nat.find_min' h,
    -- Say m = f(t)
    cases hm2 with t ht,
    -- If t>0 this is problematic
    have ht2 : t = 0,
      cases t with u, refl,
      -- because if t=u+1 then `f(f(u))<f(t)` contradicting minimality
      specialize hf u,
      specialize hm3 (f (f u)) ⟨f u, rfl⟩,
      linarith,
    -- so t=0 and hence f(0)=m
    subst ht2,
    sorry
  }
end
