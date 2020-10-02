example (P : Prop) : ∀ x ∈ (∅ : set ℕ), P :=
begin
  intro x,
  intro hx,
  cases hx,
end 

















































example (P : Prop) : ∀ x ∈ (∅ : set ℕ), P :=
begin
  intros x hx, cases hx,
end
