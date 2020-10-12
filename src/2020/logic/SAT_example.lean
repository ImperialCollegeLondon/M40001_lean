import tactic

-- First we do the question using Prop (optimised for proving)

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
  -- unprovable according to bool calc
  sorry
end

theorem trick {Q : Prop} (hQ : Q) : Q ↔ true :=
iff_of_true hQ trivial
theorem trick2 {Q : Prop} (hQ : ¬ Q) : Q ↔ false :=
iff_false_intro hQ

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
(P ∨ ¬U ∨ Q) ∧ (¬S ∨ R ∨ P) ∧ (¬P ∨ ¬Q ∨ ¬R) ∧ (¬P ∨ R ∨ ¬S)) :=
begin
  intros,
  by_cases hP : P;rw trick hP; try {rw iff_false_intro hP}; clear hP; simp;
  by_cases hP : Q;rw trick hP; try {rw iff_false_intro hP}; clear hP; simp;
  by_cases hP : R;rw trick hP; try {rw iff_false_intro hP}; clear hP; simp;
  by_cases hP : S;rw trick hP; try {rw iff_false_intro hP}; clear hP; simp;
  by_cases hP : U;rw trick hP; try {rw iff_false_intro hP}; clear hP; simp,
end

example : ∃ P Q R S U : bool, 
(Q || P || U) && (U || !Q || S) && (U || Q || !R) && (P || R || !S) &&
(P || S || R) && (R || !U || Q) && (R || S || !U) && (!S || !R || U) &&
(U || !Q || !R) && (!Q || U || !S) && (!P || !R || Q) && (S || !U || !P) &&
(!R || !P || U) && (S || !R || !U) && (!R || !Q || !S) && (Q || R || S) &&
(!U || P || !Q) && (R || !Q || !P) && (P || R || !Q) && (S || P || Q) &&
(R || P || U) && (!U || Q || R) && (!U || R || !Q) && (!S || !U || !Q) &&
(!U || !S || R) && (!S || P || U) && (P || Q || !R) && (!S || !R || U) &&
(!Q || !S || U) && (P || R || !Q) && (P || Q || !S) && (U || !S || !P) &&
(!U || R || !P) && (!U || P || !Q) && (!R || !P || S) && (R || S || !U) &&
(P || !U || Q) && (!S || R || P) && (!P || !Q || !R) && (!P || R || !S) = tt :=
begin
  simp,
  -- ⊢ false
  -- oops
  sorry
end

example : ∀ P Q R S U : bool,
(Q || P || U) && (U || !Q || S) && (U || Q || !R) && (P || R || !S) &&
(P || S || R) && (R || !U || Q) && (R || S || !U) && (!S || !R || U) &&
(U || !Q || !R) && (!Q || U || !S) && (!P || !R || Q) && (S || !U || !P) &&
(!R || !P || U) && (S || !R || !U) && (!R || !Q || !S) && (Q || R || S) &&
(!U || P || !Q) && (R || !Q || !P) && (P || R || !Q) && (S || P || Q) &&
(R || P || U) && (!U || Q || R) && (!U || R || !Q) && (!S || !U || !Q) &&
(!U || !S || R) && (!S || P || U) && (P || Q || !R) && (!S || !R || U) &&
(!Q || !S || U) && (P || R || !Q) && (P || Q || !S) && (U || !S || !P) &&
(!U || R || !P) && (!U || P || !Q) && (!R || !P || S) && (R || S || !U) &&
(P || !U || Q) && (!S || R || P) && (!P || !Q || !R) && (!P || R || !S) = ff :=
begin
  --simp -- this works
  -- but `squeeze_simp` gives information about how `simp` did it 
  -- and it tells us that this works too:
  --simp only [bnot_eq_ff_eq_eq_tt, bor_eq_false_eq_eq_ff_and_eq_ff, 
  --  bool.forall_bool, eq_self_iff_true, or_false, or_true, and_self,
  --  and_false, false_and, band_eq_false_eq_eq_ff_or_eq_ff],
  
  -- Clearly it's using reasoning. Here's a real proof by cases:
  rintros (P|P) (Q|Q) (R|R) (S|S) (T|T); -- 32 goals at this point, change `;` to `,` to see them
  refl,
end