import tactic

open function

variables (X Y Z : Type) (f : X → Y) (g : Y → Z)

example : (injective f) ∧ (injective g) → injective (g ∘ f) :=
begin
  
end
