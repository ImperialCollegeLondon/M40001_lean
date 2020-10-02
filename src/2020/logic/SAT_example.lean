import tactic

variables (P Q R S U : Prop)

example : ∃ P Q R S U : Prop, 
(Q ∨ P ∨ U) ∧ (U ∨ ¬Q ∨ S) ∧ (U ∨ Q ∨ ¬R) ∧ (P ∨ R ∨ ¬S) ∧
(P ∨ S ∨ R) ∧ (R ∨ ¬U ∨ Q) ∧ (R ∨ S ∨ ¬U) ∧ (¬S ∨ ¬R ∨ U) ∧
(U ∨ ¬Q ∨ ¬R) ∧ (¬Q ∨ U ∨ ¬S) ∧ (¬P ∨ ¬R ∨ Q) ∧ (S ∨ ¬U ∨ ¬P) ∧
(¬R ∨ ¬P ∨ U) ∧ (S ∨ ¬R ∨ ¬U) ∧ (¬R ∨ ¬Q ∨ ¬S) ∧ (Q ∨ R ∨ S) ∧
(¬U ∨ P ∨ ¬Q) ∧ (R ∨ ¬Q ∨ ¬P) ∧ (P ∨ R ∨ ¬Q) ∧ (S ∨ P ∨ Q) ∧
(R ∨ P ∨ U) ∧ (¬U ∨ Q ∨ R) ∧ (¬U ∨ R ∨ ¬Q) ∧ (¬S ∨ ¬U ∨ ¬Q) ∧
(¬U ∨ ¬S ∨ R) ∧ (¬S ∨ P ∨ U) ∧ (P ∨ Q ∨ ¬R) ∧ (¬S ∨ ¬R ∨ U) ∧
(¬Q ∨ ¬S ∨ U) ∧ (P ∨ R ∨ ¬Q) ∧ (P ∨ Q ∨ ¬S) ∧ (U ∨ ¬S ∨ ¬P) ∧
(¬U ∨ R ∨ ¬P) ∧ (¬U ∨ P ∨ ¬Q) ∧ (¬R ∨ ¬P ∨ S) ∧ (R ∨ S ∨ ¬U) ∧
(P ∨ ¬U ∨ Q) ∧ (¬S ∨ R ∨ P) ∧ (¬P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ R ∨ ¬S) :=
begin
  sorry
end

example : ∀ P Q R S U : Prop,
  ¬ (
(Q ∨ P ∨ U) ∧ (U ∨ ¬Q ∨ S) ∧ (U ∨ Q ∨ ¬R) ∧ (P ∨ R ∨ ¬S) ∧
(P ∨ S ∨ R) ∧ (R ∨ ¬U ∨ Q) ∧ (R ∨ S ∨ ¬U) ∧ (¬S ∨ ¬R ∨ U) ∧
(U ∨ ¬Q ∨ ¬R) ∧ (¬Q ∨ U ∨ ¬S) ∧ (¬P ∨ ¬R ∨ Q) ∧ (S ∨ ¬U ∨ ¬P) ∧
(¬R ∨ ¬P ∨ U) ∧ (S ∨ ¬R ∨ ¬U) ∧ (¬R ∨ ¬Q ∨ ¬S) ∧ (Q ∨ R ∨ S) ∧
(¬U ∨ P ∨ ¬Q) ∧ (R ∨ ¬Q ∨ ¬P) ∧ (P ∨ R ∨ ¬Q) ∧ (S ∨ P ∨ Q) ∧
(R ∨ P ∨ U) ∧ (¬U ∨ Q ∨ R) ∧ (¬U ∨ R ∨ ¬Q) ∧ (¬S ∨ ¬U ∨ ¬Q) ∧
(¬U ∨ ¬S ∨ R) ∧ (¬S ∨ P ∨ U) ∧ (P ∨ Q ∨ ¬R) ∧ (¬S ∨ ¬R ∨ U) ∧
(¬Q ∨ ¬S ∨ U) ∧ (P ∨ R ∨ ¬Q) ∧ (P ∨ Q ∨ ¬S) ∧ (U ∨ ¬S ∨ ¬P) ∧
(¬U ∨ R ∨ ¬P) ∧ (¬U ∨ P ∨ ¬Q) ∧ (¬R ∨ ¬P ∨ S) ∧ (R ∨ S ∨ ¬U) ∧
(P ∨ ¬U ∨ Q) ∧ (¬S ∨ R ∨ P) ∧ (¬P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ R ∨ ¬S)

  ) :=
begin
  intros,
  -- finish, -- fails
  -- UauUo!, -- fails
  sorry
end

example : ∃ P Q R S U : bool, 
(Q || P || U) && (U || ¬Q || S) && (U || Q || ¬R) && (P || R || ¬S) &&
(P || S || R) && (R || ¬U || Q) && (R || S || ¬U) && (¬S || ¬R || U) &&
(U || ¬Q || ¬R) && (¬Q || U || ¬S) && (¬P || ¬R || Q) && (S || ¬U || ¬P) &&
(¬R || ¬P || U) && (S || ¬R || ¬U) && (¬R || ¬Q || ¬S) && (Q || R || S) &&
(¬U || P || ¬Q) && (R || ¬Q || ¬P) && (P || R || ¬Q) && (S || P || Q) &&
(R || P || U) && (¬U || Q || R) && (¬U || R || ¬Q) && (¬S || ¬U || ¬Q) &&
(¬U || ¬S || R) && (¬S || P || U) && (P || Q || ¬R) && (¬S || ¬R || U) &&
(¬Q || ¬S || U) && (P || R || ¬Q) && (P || Q || ¬S) && (U || ¬S || ¬P) &&
(¬U || R || ¬P) && (¬U || P || ¬Q) && (¬R || ¬P || S) && (R || S || ¬U) &&
(P || ¬U || Q) && (¬S || R || P) && (¬P || ¬Q || ¬R) && (¬P || R || ¬S) :=
begin
  -- `simp` reduces the goal to `false`
  --  simp, 
  sorry
end

example : ∀ P Q R S U : bool, bnot ( 
  (Q || P || U) && (U || ¬Q || S) && (U || Q || ¬R) && (P || R || ¬S) &&
  (P || S || R) && (R || ¬U || Q) && (R || S || ¬U) && (¬S || ¬R || U) &&
  (U || ¬Q || ¬R) && (¬Q || U || ¬S) && (¬P || ¬R || Q) && (S || ¬U || ¬P) &&
  (¬R || ¬P || U) && (S || ¬R || ¬U) && (¬R || ¬Q || ¬S) && (Q || R || S) &&
  (¬U || P || ¬Q) && (R || ¬Q || ¬P) && (P || R || ¬Q) && (S || P || Q) &&
  (R || P || U) && (¬U || Q || R) && (¬U || R || ¬Q) && (¬S || ¬U || ¬Q) &&
  (¬U || ¬S || R) && (¬S || P || U) && (P || Q || ¬R) && (¬S || ¬R || U) &&
  (¬Q || ¬S || U) && (P || R || ¬Q) && (P || Q || ¬S) && (U || ¬S || ¬P) &&
  (¬U || R || ¬P) && (¬U || P || ¬Q) && (¬R || ¬P || S) && (R || S || ¬U) &&
  (P || ¬U || Q) && (¬S || R || P) && (¬P || ¬Q || ¬R) && (¬P || R || ¬S)) :=
begin
  -- simp works
  simp
  --squeeze_simp,
end #exit
  intros,
  cases P;
  cases Q;
  cases R;
  cases S;
  cases U;
  simp,
end