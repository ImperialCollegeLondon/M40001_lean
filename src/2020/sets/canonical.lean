import tactic

/- Let α be a fixed ground set, which is a type.

   There is a bijection between
   (a) the type `α → Prop` whose terms
         are functions from `α` to `Prop`, and
   (b) the type `set α`, whose terms
         are subsets of α.
-/
def canonical (α : Type) : (α → Prop) ≃ (set α) :=
{ to_fun := 
  -- construction A
    -- let P be a function from α to Prop
  λ P,
    -- Then return the subset {x | P x} of α
  {x : α | P x},
  inv_fun := 
  -- construction B
    -- let X be a subset of α,
  λ X,
    -- and let's define a function from α to Prop.
    -- So say x is in α,
  λ a,
    -- and we're supposed to be returning a Prop,
    -- so let's return `a ∈ X`
    a ∈ X,
  left_inv := begin
    intro P,
    ext a,
    dsimp,
    refl,  
  end
  ,
  right_inv := begin
    intro X,
    refl,
  end }
  