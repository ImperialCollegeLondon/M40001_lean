import tactic

-- Let X be the set {A,B,C}
@[derive fintype] inductive X
| A : X
| B : X
| C : X

open X

inductive R : X → X → Prop
| AB : R A B
| AC : R A C

instance : decidable_rel R :=
begin
  unfold decidable_rel,
  intros a b,
  cases a; cases b;
  [left, right, right, left, left, left, left, left, left];
  exact R.AB <|> exact R.AC <|> rintro (_ | _),
end

instance : decidable (transitive R) :=
begin
  unfold transitive,
  apply_instance,
end

theorem R_fst {x y : X} : R x y → x = A :=
begin
  rintro (hAB | hAC); refl
end

example : transitive R :=
begin
  exact dec_trivial,
  -- human proof below

  -- intros p q r,
  -- intros hpq hqr,
  -- have hp := R_fst hpq,
  -- subst hp,
  -- have hq := R_fst hqr,
  -- subst hq,
  -- assumption,
end

