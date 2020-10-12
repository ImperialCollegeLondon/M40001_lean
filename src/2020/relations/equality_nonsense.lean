import tactic

variables (α : Type) (x y z : α)

--set_option pp.notation false
example : x = x :=
begin
  refl,
end


example : x = y → y = x :=
begin
  intro h,
  induction h,
  refl,
end

example : x = y → y = z → x = z :=
begin
  intro hxy,
  intro hyz,
  induction hxy,
  assumption,
end



