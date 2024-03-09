import tactic

namespace relations_2022_pals

/-

# Solution to the `pals` question

Let X be a fixed set. If φ : X → A is a function then let’s define the equivalence relation
Rφ on X associated to φ by Rφ(s, t) ⇐⇒ φ(s) = φ(t) (you can check it’s an equivalence
relation if you like). Of course as φ and A vary we can get lots of different equivalence relations
on X in this way.
We say two surjections f : X → Y and g : X → Z are pals if there exists a bijection h : Y → Z
such that g = h ◦ f . Prove that f and g are pals if and only if the equivalence relations Rf
and Rg on X associated to f and g are equal (by which I mean that for all s, t ∈ X, we have
Rf (s, t) ⇐⇒ Rg(s, t)).
-/

-- Let `X` be a set
constant X : Type

-- Let `S` be the set of triples consisting of a set, and a surjection from `X` to that set
structure S :=
(Y : Type)
(f : X → Y)
(hf : f.surjective)

-- Internally an element `a` of `S` is a set `a.Y`, a function `a.f : X → a.Y` and
-- a proof `a.hf` that `a.f` is surjective. But we would like to treat elements of `S`
-- as functions! More precisely we want `a` to be identified with the function `a.f`
-- when we treat it as a function. So let's tell this to Lean
instance : has_coe_to_fun S (λ a, X → a.Y) := ⟨λ a, a.f⟩

-- Let's define what it means for two elements of S to be pals
def pals (a b : S) : Prop :=
-- Say f : X → Y and g : X → Z are in S
let ⟨Y, f, hf⟩ := a, ⟨Z, g, hg⟩ := b in 
-- Then they're pals iff there exists a bijection `h` from Y to Z
-- such that `∀ x, g(x)=h(f(x))
∃ h : Y ≃ Z, ∀ x : X, g x = h (f x)

-- The claim: Two surjections are pals if and only if their associated binary relations
-- are equal in the sense of binary relations
theorem pals_iff_relations_equal : ∀ f g : S, pals f g ↔ ∀ s t : X,
  f s = f t ↔ g s = g t :=
begin
  -- Let `f : X → Y` and `g : X → Z` be surjections.
  rintro ⟨Y, f, hf⟩ ⟨Z, g, hg⟩,
  -- We need to prove the implications in both directions
  split,
  { -- First let's assume `f` and `g` are pals, and that `h` is the associated 
    -- bijection
    rintro ⟨h, hpals⟩,
    -- We now need to prove that if x₁ and x₂ are arbitrary elements of X,
    rintro x₁ x₂,
    -- then f x₁ = f x₂ ↔ g x₁ = g x₂
    show f x₁ = f x₂ ↔ g x₁ = g x₂,
    -- Well, we know g = h ∘ f so we need to show
    -- f x₁ = f x₂ ↔ h (f x₁) = h (f x₂)
    simp only [hpals],
    -- Left to right is obvious
    split, rintro h, rw h,
    -- Right to left is exactly injectivity of `h`,
    apply h.injective, },  
  { -- Now the other way: assume that ∀ x₁ and x₂, f x₁ = fx₂ ↔ g x₁ = g x₂
    rintro hrel : forall x₁ x₂, f x₁ = f x₂ ↔ g x₁ = g x₂,
    -- Let's prove that `f` and `g` are pals by finding a bijection from `Y` to `Z`.
    -- We know that `f` is surjective, so `∀ y ∈ Y, ∃ x ∈ X with f(x)=y. 
    -- Let's define `finv : Y → X` by letting `finv(y)` be an arbitrary element
    -- `x` of `X` such that `f(x)=y`. By definition of `finv` we know that
    -- `∀ y ∈ Y, f(finv y)=y`. Let's call this `hyp1`. Note that this does
    -- *not* imply that `finv` is a *two-sided* bijection for `f`, as we don't
    -- know that `finv(f(x))=x` in general. 
    choose finv hyp1 using hf,
    -- Similarly let's define `ginv : Z → X` such that `∀ z ∈ Z, g (ginv z)=z`,
    -- and let's let `hyp2` denote this statement.
    choose ginv hyp2 using hg,
    -- Let's define `h : Y → Z` to be `g ∘ finv`
    -- and let's define `j : Z → Y` to be `f ∘ ginv`
    let h : Y → Z := g ∘ finv,
    let j : Z → Y := f ∘ ginv,
    -- I claim that `h` and `j` are two-sided inverses, and hence `h` is a bijection.
    -- Let's first show that this claim implies that `f` and `g` are pals.
    suffices : j.left_inverse h ∧ j.right_inverse h,
    { -- Of course we use `h`
      use ⟨h, j, this.1, this.2⟩,
      -- and now we have to prove that ∀ x, g(x)=h(f(x))
      intro x,
      show g(x)=h(f(x)),
      -- Well by definition h=g∘finv
      show g(x)=g(finv(f(x))),
      -- and we know g(x₁)=g(x₂) ↔ f(x₁)=f(x₂)
      rw ← hrel,
      -- so it suffices to prove f(x)=f(finv(f(x))),
      -- but this is immediate from `hyp1`
      rw hyp1, },
    -- It remains to prove that `h` and `j` are two-sided inverses.
    split,
    { -- Let's start by showing that ∀ y ∈ Y, j(h(y))=y. Let y ∈ Y be arbitrary.
      intro y,
      -- By definition of j and h, we need to show that f(ginv(g(finv(y))))=y
      show f (ginv (g (finv(y)))) = y,
      -- By hyp1, we know y=f(finv(y)), so we need to show f(ginv(g(finv(y))))=f(finv(y))
      conv_rhs {rw ← hyp1 y},
      -- But we know f(x₁)=f(x₂) ↔ g(x₁)=g(x₂) so we can replace the first f's by g's
      rw hrel,
      -- and now we can cancel g ∘ ginv because of hyp2, and we're done
      rw hyp2, },
    { -- The other way is pretty much exactly the same
      intro z,
      conv_rhs {rw ← hyp2 z},
      rw [← hrel, hyp1], } }
end

end relations_2022_pals
