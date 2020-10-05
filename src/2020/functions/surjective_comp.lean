import tactic

open function

variables (X Y Z : Type) (f : X → Y) (g : Y → Z)

example : (surjective f) ∧ (surjective g) → surjective (g ∘ f) :=
begin
      -- Say f and g are surjective.
  rintros ⟨hf, hg⟩,
      -- Choose  z in Z.
  intro z,
      -- Our job is to find x in X such that g(f(x))=z.

      -- Well g is assumed surjective so we can find y in Y
      -- such that g(y)=z
  rcases hg z with ⟨y, rfl⟩,

      -- And f is assumed surjective so we can find x in X
      -- such that f(x)=y
  rcases hf y with ⟨x, rfl⟩,

   -- let's use this x.
  use x,
      -- and now we see g(f(x))=g(y)=z so we're done
end