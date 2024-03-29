import tactic

/-- The equivalence relation on ℕ² such that equivalence classes are ℤ -/
def nat2.R (a b : ℕ × ℕ) : Prop :=
a.1 + b.2 = b.1 + a.2
-- here a and b are pairs, so a = (a.1, a.2) etc.

-- introduce ≈ (type with `\~~`) notation for this relation
instance : has_equiv (ℕ × ℕ) := ⟨nat2.R⟩

-- let's prove some lemmas about this binary relation
namespace nat2.R
#check quotient.lift_on
-- The following lemma is true by definition, but it's useful to
-- have it around so you can rewrite with it
@[simp] lemma equiv_def {i j k l : ℕ} : (i, j) ≈ (k, l) ↔ i + l = k + j :=
begin
  refl
end

-- try rewriting `equiv_def`
lemma practice : (3, 5) ≈ (4, 6) :=
begin
  change 3 + 6 = 4 + 5,
  refl,
end

-- Now let's prove that this binary relation is an equivalence relation
lemma reflexive : ∀ x : ℕ × ℕ, x ≈ x :=
begin
  rintro ⟨i, j⟩,
  rw equiv_def,
end

lemma symmetric : ∀ x y : ℕ × ℕ, (x ≈ y) → (y ≈ x) :=
begin
  -- here are a couple of tricks
  rintro ⟨i, j⟩ ⟨k, l⟩ h,
  -- type `⊢` with `\|-` 
  rw equiv_def at h ⊢,
  rw h,
end

lemma transitive : ∀ x y z : ℕ × ℕ, (x ≈ y) → (y ≈ z) → (x ≈ z) :=
begin
  -- this is a little trickier
  -- recall `add_right_inj` says `a + b = c + b → a = c`
  rintro ⟨i, j⟩ ⟨k, l⟩ ⟨m, n⟩ hxy hyz,
  rw equiv_def at hxy hyz ⊢,
  rw ← add_left_inj (k+l),
  calc (i+n)+(k+l)=(i+l)+(k+n) : by ring
  ... = (k+j)+(m+l) : by rw [hxy, hyz]
  ... = (m+j)+(k+l) : by ring
end

-- This line tells Lean that the binary relation is an equivalence
-- relation and hence we can take the "quotient", i.e. the
-- type of equivalence classes
instance setoid : setoid (ℕ × ℕ) :=
{ r := nat2.R,
  iseqv := ⟨reflexive, symmetric, transitive⟩ }

-- end of lemmas about the binary relation
end nat2.R

-- ...but we're still going to be using them
open nat2.R

/-- The integers are the equivalence classes of the equivalence relation
 we just defined on ℕ²  -/
def myint := quotient nat2.R.setoid

-- let's make some definitions, and prove some theorems, about integers
namespace myint 

-- The first goal is to get a good interface for addition.
-- To do this we need to define a+b, and -a, and 0. Let's do
-- them in reverse order.

/-! ## zero -/

def zero := ⟦(0,0)⟧

instance : has_zero myint := ⟨myint.zero⟩

lemma zero_def : (0 : myint) = ⟦(0, 0)⟧ :=
begin
  refl
end

/-! ## negation (additive inverse) -/

-- First we define an "auxiliary" map from ℕ² to ℤ 
-- sending (a,b) to the equivalence class of (b,a).

def neg_aux (x : ℕ × ℕ) : myint := ⟦(x.2, x.1)⟧

-- true by definition
lemma neg_aux_def (i j : ℕ) : neg_aux (i, j) = ⟦(j, i)⟧ := rfl

/-! ### Well-definedness

OK now here's the concrete problem. We would like to define
a negation map `ℤ → ℤ` sending `z` to `-z`. We want to do this in
the following way: Say `z ∈ ℤ`. Choose `a=(i,j) ∈ ℕ²` representing `z`
(i.e. such that `cl(i,j) = ⟦(i,j)⟧ = z`)
Now apply `neg_aux` to `a`, and define `-z` to be the result.

The problem with this is that what if `b` is a different
element of the equivalence class? Then we also want `-z` to be `neg_aux b`.

Indeed, in Lean this construction is called `quotient.lift`, and
if you uncomment the below code
-/

--def neg : myint → myint :=
--quotient.lift neg_aux _

/-
you'll see an error, and if you put your cursor on the error you'll
see that Lean wants a proof that if two elements `a` and `b` are in the
same equivalence class, then `neg_aux a = neg_aux b`. So let's prove this now.
-/

-- negation on the integers, defined via neg_aux, is well-defined.
lemma neg_aux_lemma : ∀ x y : ℕ × ℕ, x ≈ y → neg_aux x = neg_aux y :=
begin
  rintro ⟨i,j⟩ ⟨k,l⟩ h,
  rw [neg_aux_def, neg_aux_def],
  -- ⊢ ⟦(j, i)⟧ = ⟦(l, k)⟧
  -- next step: if ⟦a⟧=⟦b⟧ then a ≈ b
  apply quotient.sound,
  -- ⊢ (j, i) ≈ (l, k)
  rw equiv_def at h ⊢,
  rw add_comm,
  rw ← h,
  apply add_comm,
end

/-- Negation on on the integers. The function sending `z` to `-z`. -/
def neg : myint → myint :=
quotient.lift neg_aux neg_aux_lemma

-- notation for negation
instance : has_neg myint := ⟨neg⟩

-- this is true by definition
lemma neg_def (i j : ℕ) : (-⟦(i, j)⟧ : myint) = ⟦(j, i)⟧ :=
begin
  refl
end

/-!  ## addition

Our final construction: we want to define addition on `myint`. 
Here we have the same problem. Say z₁ and z₂ are integers.
Choose elements a₁=(i,j) and a₂=(k,l) in ℕ². We want to define
z₁ + z₂ to be ⟦(i+k,j+l)⟧, the equivalence class of a₁ + a₂.
Let's make this definition now.

-/

/-- An auxiliary function taking two elements of ℕ² and returning
the equivalence class of their sum. -/
def add_aux (x y : ℕ × ℕ) : myint := ⟦(x.1 + y.1, x.2 + y.2)⟧

-- true by definition, but useful for rewriting
lemma add_aux_def (i j k l : ℕ) : add_aux (i, j) (k, l) = ⟦(i + k, j + l)⟧ :=
begin
  refl
end

/-

We want the definition of addition to look like the below.
Uncomment it to see the problem. 

-/

--def add : myint → myint → myint :=
--quotient.lift₂ add_aux _

/-
We had better check that choosing different elements in the same
equivalence class gives the same definition.

-/

lemma add_aux_lemma : ∀ x₁ x₂ y₁ y₂ : ℕ × ℕ,
(x₁ ≈ y₁) → (x₂ ≈ y₂) → add_aux x₁ x₂ = add_aux y₁ y₂ :=
begin
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨g, h⟩ h1 h2,
  rw add_aux_def,
  rw add_aux_def,
  apply quotient.sound,
  rw equiv_def at *,
  rw (show (a+c)+(f+h) = (a+f)+(c+h), by ring),
  rw [h1, h2],
  ring,
end

-- Now this is checked, we can define addition.

/-- Addition on the integers -/
def add : myint → myint → myint :=
quotient.lift₂ add_aux add_aux_lemma

-- notation for addition
instance : has_add myint := ⟨add⟩

-- true by definition
lemma add_def (i j k l : ℕ) :
  (⟦(i, j)⟧ + ⟦(k, l)⟧ : myint) = ⟦(i + k, j + l)⟧ :=
begin
  refl
end

/-
The four fundamental facts about addition on the integes are:
1) associativity
2) commutativity
3) zero is an additive identity
4) negation is an additive inverse.

Let's prove these now.

-/

lemma zero_add (x : myint) : 0 + x = x :=
begin
  apply quotient.induction_on x,
  rintro ⟨a, b⟩,
  rw zero_def,
  rw add_def,
  apply quotient.sound,
  rw equiv_def,
  ring,
end

lemma add_zero (x : myint) : x + 0 = x :=
begin
  apply quotient.induction_on x,
  rintro ⟨a, b⟩,
  rw zero_def,
  rw add_def,
  apply quotient.sound,
  rw equiv_def,
  ring,
end

lemma add_left_neg (x : myint) : -x + x = 0 :=
begin
  apply quotient.induction_on x,
  rintro ⟨a, b⟩,
  rw zero_def,
  rw neg_def,
  rw add_def,
  apply quotient.sound,
  rw equiv_def,
  ring,
end

lemma add_comm (x y : myint) : x + y = y + x :=
begin
  apply quotient.induction_on₂ x y,
  rintro ⟨a, b⟩ ⟨c, d⟩,
  rw [add_def, add_def],
  apply quotient.sound,
  rw equiv_def,
  ring,
end

lemma add_assoc (x y z : myint) : (x + y) + z = x + (y + z) :=
begin
  apply quotient.induction_on₃ x y z,
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩,
  simp [add_def],
  ring,
end

-- We just proved that the integers are a commutative group under addition!

instance : add_comm_group myint :=
{ add := (+),
  add_assoc := add_assoc,
  zero := 0,
  zero_add := zero_add,
  add_zero := add_zero,
  neg := has_neg.neg,
  add_left_neg := add_left_neg,
  add_comm := add_comm }

-- woohoo!

/-! ## multiplication

What's left to define is 1 and multiplication (note that we don't need multiplicative
inverses -- if a is a non-zero integer then a⁻¹ is typially not an integer)

-/

def mul_aux (x y : ℕ × ℕ) : myint := ⟦(x.1*y.1+x.2*y.2, x.1*y.2+x.2*y.1)⟧

lemma mul_aux_def (i j k l : ℕ) : mul_aux (i, j) (k, l) = ⟦(i*k+j*l, i*l+j*k)⟧ :=
begin
  refl
end

-- Boss level. 
-- Dr. Lawn: "We leave the similar verification for multiplication as an exercise."

-- This is what we need to check for multiplication to "descend" (or "lift" as Lean
-- calls it) to a well-defined function on the quotient. 
lemma mul_aux_lemma : ∀ x₁ x₂ y₁ y₂ : ℕ × ℕ,
(x₁ ≈ y₁) → (x₂ ≈ y₂) → mul_aux x₁ x₂ = mul_aux y₁ y₂ :=
begin
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨g, h⟩ h1 h2,
  simp only [mul_aux_def],
  apply quotient.sound,
  rw equiv_def at *,
  -- a calc proof would be nicer. Can I get away with rewriting h1 and h2
  -- fewer times?
  rw ← add_left_inj (a * h),
  have h3 : a * c + b * d + (e * h + f * g) + a * h = a * (c + h) + b*d+e*h+f*g,
    ring,
  rw h3,
  rw h2,
  have h4 : a * (g + d) + b * d + e * h + f * g = (a+f)*g+a*d+b*d+e*h,
    ring,
  rw h4,
  rw h1,
  clear h3, clear h4,
  rw (show (e + b) * g + a * d + b * d + e * h = e*g+a*d+b*(g+d)+e*h, by ring),
  rw ← h2,
  rw (show e * g + a * d + b * (c + h) + e * h = e * g + a * d + b * c + (e+b) * h, by ring),
  rw ← h1,
  ring,
end

-- definition of multiplication
def mul : myint → myint → myint :=
quotient.lift₂ mul_aux mul_aux_lemma

instance : has_mul myint := ⟨mul⟩ 

lemma mul_def (i j k l : ℕ) : (⟦(i, j)⟧ * ⟦(k, l)⟧ : myint) = ⟦(i*k+j*l, i*l+j*k)⟧ :=
begin
  refl
end

lemma mul_assoc (x y z : myint) : (x * y) * z = x * (y * z) :=
begin
  apply quotient.induction_on₃ x y z,
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩,
  simp [mul_def],
  ring,
end

def one : myint := ⟦(37, 36)⟧

instance : has_one myint := ⟨myint.one⟩

-- true by definition
lemma one_def : (1 : myint) = ⟦(37, 36)⟧ :=
begin
  refl
end

lemma one_mul (x : myint) : 1 * x = x :=
begin
  apply quotient.induction_on x,
  rintro ⟨i, j⟩,
  simp [one_def, mul_def],
  ring,
end

lemma mul_one (x : myint) : x * 1 = x :=
begin
  apply quotient.induction_on x,
  rintro ⟨i, j⟩,
  simp [one_def, mul_def],
  ring,
end

lemma mul_comm (x y : myint) : x * y = y * x :=
begin
  apply quotient.induction_on₂ x y,
  rintro ⟨i, j⟩ ⟨k, l⟩,
  simp [mul_def],
  ring,
end

lemma mul_add (x y z : myint) : x * (y + z) = x * y + x * z :=
begin
  apply quotient.induction_on₃ x y z,
  rintro ⟨i, j⟩ ⟨k, l⟩ ⟨m, n⟩,
  simp [add_def, mul_def],
  ring,
end

lemma add_mul (x y z : myint) : (x + y) * z = x * z + y * z :=
begin
  apply quotient.induction_on₃ x y z,
  rintro ⟨i, j⟩ ⟨k, l⟩ ⟨m, n⟩,
  simp [add_def, mul_def],
  ring,
end

-- The integers are a commutative ring
-- (that is, they satisfy the axioms we just proved)
instance : comm_ring myint :=
{ mul := (*),
  mul_assoc := mul_assoc,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  left_distrib := mul_add,
  right_distrib := add_mul,
  mul_comm := mul_comm,
  ..myint.add_comm_group }

end myint

