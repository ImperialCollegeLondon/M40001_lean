open function

example
  (X Y Z : Type)
  (f : X → Y)
  (g : Y → Z)
  (f_inj : injective f)
  (g_inj : injective g) :
injective (g ∘ f) :=
begin
  unfold injective at *,
  intros p q,
  intro h,
  apply f_inj,
  apply g_inj,
  exact h,
end

example
  (X Y Z : Type)
  (f : X → Y)
  (g : Y → Z)
  (f_surj : surjective f)
  (g_surj : surjective g) :
surjective (g ∘ f) :=
begin
  intro z,
  cases (g_surj z) with y hy,
  cases (f_surj y) with x hx,
  existsi x,
  rw ←hy,
  rw ←hx,
end