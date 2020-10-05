import tactic

open function

variables (X Y Z : Type) (f : X → Y) (g : Y → Z)

example : (injective f) ∧ (injective g) → injective (g ∘ f) :=
begin
  -- Assume that f and g are injective.
  rintro ⟨hf, hg⟩,
  -- We need to prove `g ∘ f` is injective.
  -- So say `a`, `b` are in `X`, and `(g ∘ f)(a) = (g ∘ f)(b)` 
  rintro a b hab,
  -- We need to prove that `a = b`.
  -- By injectivity of `f`, it suffices to prove that `f(a) = f(b)`.
  apply hf,
  -- But this follows immediately from our assumption `g(f(a))=g(f(b))`,
  -- and injectivity.
  exact hg hab,
end