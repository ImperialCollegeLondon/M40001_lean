import tactic

@[derive fintype] inductive bool2
| ff2 : bool2
| tt2 : bool2

namespace bool2

definition and2 : bool2 → bool2 → bool2
| ff2 P := ff2
| tt2 P := P

definition or2 : bool2 → bool2 → bool2
| tt2 P := tt2
| ff2 P := P

definition not2 : bool2 → bool2
| tt2 := ff2
| ff2 := tt2

definition xor2 (x y : bool2) := and2 (or2 x y) (not2 (and2 x y))

definition going : bool2 → bool
| ff2 := tt
| tt2 := ff

end bool2

open bool2

definition bool.to2 : bool → bool2
| tt := ff2
| ff := tt2

namespace bool2

-- no good -- false and true name clash

-- `bool2.F`, standing for "From `bool` (to `bool2` in this case)".

-- `bool2.T`, standing for "To `bool` (from `bool2` in this case)"
-- So anything we can do in `bool` about `bool2` 

-- These functions bijectively identify `bool` and `bool2`.

open bool

definition equiv : bool2 ≃ bool :=
{ to_fun := going,
  inv_fun := to2,
  left_inv := begin
    intro x,
    cases x;
    refl,
  end,
  right_inv := begin
    rintro (ht | hf);
    refl
  end
   }
end bool2

-- every definition involving bool has a corresponding definition
-- in bool2

-- What construction in `bool2` corresponds to `and` in `bool`?

example (x y : bool) : (x && y).to2 = or2 x.to2 y.to2 :=
begin
  cases x;
  cases y;
  refl,
end

example (x y : bool) : (x || y).to2 = and2 x.to2 y.to2 :=
begin
  cases x;
  cases y;
  refl,
end

example (x y : bool) : (bxor x y).to2 = not2 (xor2 x.to2 y.to2) :=
begin
  cases x;
  cases y;
  refl,
--  sorry,sorry,sorry,sorry,
end

#print prefix bool
example (x : bool) : (bnot x).to2 = not2 (x.to2) :=
begin
  cases x;
  refl
end

def bimp : bool → bool → bool
| ff tt := ff
| _  _  := tt

-- corresponds to something awful

-- Computer scientists don't want to reason about bool
-- or prove theorems about it -- they just need it
-- to make data structures, recording yes-no answers
-- to questions about the terms involved.

example (b : bool) : b = ff ∨ b = tt := bool.dichotomy b

-- I can'y do this -- ask Chris?
example : ∀ f : bool → bool → bool, 
  (∀ x y : bool, f x y = f y x) → 
  (f = bor ∨ f = band ∨ f = bxor ∨ f = λ x y, bnot (band x y) 
  ∨ f = λ x y, bnot (bor x y) ∨ f = λ x y, bnot (bxor x y) ∨ f = λ x y, tt ∨ f = λ x y, ff) :=
begin
  intros,
  rw function.funext_iff,
  rw function.funext_iff,
  rw function.funext_iff,
  rw function.funext_iff,
  cases (f tt tt).dichotomy;
  cases (f tt ff).dichotomy;
  cases (f ff tt).dichotomy;
  cases (f ff ff).dichotomy,

  { 
    sorry },
  repeat {sorry},
  
--  exact dec_trivial,
end

-- now let's see forall and exists
variables (Ω : Type) (X Y : set Ω)

example : ¬ (∃ a, X a) ↔ ∀ b, ¬ (X b) :=
begin
  split,
  { intro h,
    intros b hb,
    apply h,
    use b,
    assumption },
  { intro h,
    intro h2,
    cases h2 with a ha,
    apply h a,
    assumption },
end
example : ¬ (∀ a, X a) ↔ ∃ b, ¬ (X b) :=
begin
  split,
  { -- classical
    intro h,
    classical,
    by_contra hnX,
    apply h,
    intro a,
    by_contra hXa,
    apply hnX,
    use a }, 
  { intro h,
    cases h with b hb,
    intro h,
    apply hb,
    apply h }
end

example : ¬ (∃ a, X a) ↔ ∀ b, ¬ (X b) :=
begin
  split,
  { intro h,
    intros b hb,
    apply h,
    use b,
    assumption },
  { intro h,
    intro h2,
    cases h2 with a ha,
    apply h a,
    assumption },
end

