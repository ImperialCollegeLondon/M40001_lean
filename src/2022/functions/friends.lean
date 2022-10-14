import tactic

/-

# Solution to the "friends" problem in Lean

## The question

Let `Z` be a set. If `f : X → Z` and `g : Y → Z` are injective functions, let’s say that `f` is
friends with `g` if there is a bijection `h : X → Y` such that `f = g ∘ h`.

Prove that f is friends with g if and only if the range of f equals the range of g. 

NB: by the range of f : X → Z I mean the subset of Z consisting of things “hit” by f ,
in other words the set `{z : Z | ∃ x : X, f x = z}`. Some people call this the “image” of f , 
and some people use “range” to mean the same thing as “codomain” :-|

-/

-- Let Z be a set, fixed throughout this question
constant Z : Type

-- Let S be the set of collections of a set `X` and an injective function `X → Z`
structure S :=
(X : Type)
(f : X → Z)
(hf : f.injective)

-- Implementation detail:
-- The way `S` works internally is is that an element `s` of `S` is a triple consisting
-- of a set `s.X`, a function `s.f : s.X → Z` and a proof `s.hf` that `s.f` is injective.
-- We will *abuse* notation by talking about elements of `S` as functions, but really
-- an element of `S` is a triple.

-- Say elements `f : X → Z` and `g : Y → Z` of `S` are *friends* if there's a bijection
-- `h` from `X` to `Y` such that forall `x` in `X`, `f(x)=g(h(x))`
def friends (f g : S) : Prop :=
-- take f and g apart into their triples 
let ⟨X, f, hf⟩ := f, ⟨Y, g, hg⟩ := g in 
-- and now write the definition
∃ h : X ≃ Y, ∀ x : X, f x = g (h x)

open set

-- Before we start on the theorem, let's prove some helpful lemmas.

-- First let's first prove that if `f` is friends with `g` then `g` is friends with `f`
lemma friends_symmetric : ∀ f g : S, friends f g → friends g f :=
begin
  -- let's say `f` is represented by `f : X → Z`, with proof `hf` that `f` is injective
  rintro ⟨X, f, hf⟩, 
  -- and let's say `g` is represented by `g : Y → Z`
  rintro ⟨Y, g, hg⟩,
  -- Let `h` be the function showing that `f` and `g` are friends
  rintro ⟨h, hfriends⟩,
  -- h is bijective so it has a two-sided inverse; let's use that to show that 
  -- `g` and `f` are friends
  use h.symm,
  -- Our hypotheses `hfriends` is that `∀ x, f(x)=g(h(x))`, and we have to show
  -- that `∀ y, g(y)=f(h⁻¹(y))`. So let y ∈ Y be arbitrary
  intro y,
  -- Apply `hfriends` with `x=h⁻¹(y)
  rw hfriends,
  -- We now have to prove that g(y)=g(h(h⁻¹(y))) but the h and h⁻¹ now cancel
  -- because h⁻¹ is a two-sided inverse of h, so we're done
  simp,
end

-- Now let's prove that if `f` is friends with `g` then the range of `f` is a
-- subset of the range of `g`
lemma friends_implies_subset : ∀ f g : S, friends f g → range f.f ⊆ range g.f :=
begin
  -- Let f : X → Z and g : Y → Z be friends and let `h : X → Y` be the bijection
  rintro ⟨X, f, hf⟩ ⟨Y, g, hg⟩ ⟨h, hfriends⟩,
  -- We need to prove range(f) ⊆ range(g), so say z ∈ range(f)
  rintro z (hz : z ∈ range f),
  -- Because `z` is in the range of `f`, there exists `x ∈ X` with `f(x)=z`.
  obtain ⟨x, rfl⟩ := hz,
  -- The goal is to prove that f(x) is in the range of g. Let's show that it
  -- equals g(h(x)).
  refine ⟨h x, (_ : g (h x) = f x)⟩,
  -- But this follows immediately from the fact that `f` and `g` are friends.
  rw hfriends,
end

-- The big theorem: two injective functions f and g are friends iff they have
-- the same range
theorem friends_iff_same_range (f g : S) : friends f g ↔ range f.f = range g.f :=
begin
  -- This is an iff so let's first go one way and then the other
  -- First let's prove that if a and b are friends then their ranges are the same
  split,
  { -- Assume f and g are friends
    intro hfriends,
    -- To prove that two sets are equal, it suffices to prove that each one
    -- is a subset of the other
    apply subset_antisymm,
    { -- One inclusion follows from the lemma `friends_implies_subset`
      apply friends_implies_subset,
      assumption, },
    { -- and the other also follows from the lemma `friends_implies_subset`,
      apply friends_implies_subset,
      -- and the fact that g is friends with f, which follows from the lemma `friends_symmetric`
      apply friends_symmetric,
      assumption, } },
  { -- Now let's go the other way
    -- Say f : X → Z and g : Y → Z are injective functions with the same range
    rcases f with ⟨X, f, hf⟩,
    rcases g with ⟨Y, g, hg⟩,
    rintro (hrange : range f = range g),
    -- Let's prove that `f` and `g` are friends.
    -- We need to construct a bijection from X to Y.
    -- First let's show that for all x in X, there exists y in Y with g(y)=f(x)
    have hxy : ∀ x : X, ∃ y : Y, g y = f x,
    { -- so let x ∈ X be arbitrary
      intro x,
      -- Then by definition, f(x) ∈ range f
      have hx : f x ∈ range f := ⟨x, rfl⟩,
      -- so f(x) ∈ range g, because hypothesis `hrange` says that `f` and `g` have the same range
      rw hrange at hx,
      -- and hence there exists y ∈ Y with g(y)=f(x)
      exact hx, },
    -- Using this fact let's define h : X → Y by, for all x in X, letting h(x) be an
    -- arbitrary element `y` of `Y` with `g(y)=f(x)`.
    -- We note that this definition shows that `∀ x, g(h(x))=f(x)`. 
    -- Let's call this hypothesis `hyp1`
    choose h hyp1 using hxy,
    -- The same construction with X and Y reversed
    -- shows that for all y in Y, there exists x in X with f(x)=g(y)
    have hyx : ∀ y : Y, ∃ x : X, f x = g y,
    { intro y,
      have hy : g y ∈ range g := ⟨y, rfl⟩,
      rwa ← hrange at hy, },
    -- So we can define j : Y → X by, for all y ∈ Y, letting j(y) ∈ X be an arbitrary
    -- element of X with f(x)=g(y). In other words, we know that for all y, `f(j(y))=g(y)`
    -- Let's let `hyp2` be the statement `∀ y, f(j(y))=g(y)`.
    choose j hyp2 using hyx,
    -- I claim is that ``h` and `j` are two-sided inverses of one another,
    -- and hence `h` is a bijection. 
    -- Let's first check that the claim implies that f and g are friends.
    suffices : j.left_inverse h ∧ j.right_inverse h,
    { -- What needs to be done to check that `h : X → Y` works?
      refine ⟨⟨h, j, this.1, this.2⟩, _⟩,
      -- We just need to prove that ∀ x, f(x)=g(h(x))
      show ∀ x, f x = g (h x),
      -- But this is just `hyp1`,
      intro x, rw hyp1,
    },
    -- It suffices to prove that `j` is both a left and right inverse of `h`.
    split,
    { -- Let's first show that j(h(x))=x for all x. So let x in X be arbitrary
      intro x,
      -- By injectivity of f, it suffices to prove that f(j(h(x)))=f(x)
      apply hf,
      -- Now use hyp2, which says f ∘ j = g
      rw hyp2,
      -- and now the goal is ∀ x, g(h(x))=f(x), which is hypothesis `hyp1`
      rw hyp1,
    },
    { -- The other way is pretty much the same. We need to show h(j(y))=y for all y.
      -- So let y be arbitrary
      intro y,
      -- By injectivity of g, it suffice to prove g(h(j(y)))=g(y)
      apply hg,
      -- but g∘h=f by hyp1
      rw hyp1,
      -- and f(j(y))=g(y) by hype
      rw hyp2,
      -- and we're done!
    } },
  
end


