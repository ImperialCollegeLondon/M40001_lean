import tactic

-- notation for products

-- enter the product namespace

namespace prod

variables (X Y : Type)

-- Notation for product is `×`, `\times` in VS Code
#check X × Y -- Type. 

-- notation for elements

variables (x : X) (y : Y)

/-! ## The Data -/

-- this is notation for `prod.mk`, the function which constructs
-- an element of X × Y from an element of `X` and an eleent of `Y`
#check (x, y) -- X × Y

-- The projections are called `fst` and `snd`.

#check prod.fst
#check prod.snd

-- but "dot notation" `a.1` and `a.2` are used more often if `a : X × Y`
-- The 
#check prod
--#print prefix prod
#check @mk

/-! ## The proofs that it satisfies the axioms for product -/

-- this one is true by definition but actually
-- using definitional equality is in some
-- sense cheating the system
example : (x, y).1 = x :=
begin
  refl
end

-- this one is true by something
example (a : X × Y) : (a.1, a.2) = a :=
begin
  apply mk.eta, -- this axiom is called "eta conversion"
end

/-! ## the universal property -/

#check @prod.rec

-- universal property
example : ∀ (T : Type) (f : T → X) (g : T → Y),
∃! h : T → X × Y, prod.fst ∘ h = f ∧ prod.snd ∘ h = g :=
begin
  intros,
  use [λ t, (f t, g t)],
  -- tidy works now
  split,
    split,
      refl,
    refl,
  rintro j ⟨rfl,rfl⟩,
  funext t,
  apply mk.eta.symm,
end

end prod