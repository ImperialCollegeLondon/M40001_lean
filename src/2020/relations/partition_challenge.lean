import data.equiv.basic
import tactic


/-!

# Definition and basic API for partitions

-/

/- 

## Definition of a partition

Let `α` be a type. A *partition* on `α` is defined to be
the following data:

1) A set C of subsets of α, called "blocks".
2) A hypothesis (i.e. a proof!) that all the blocks are non-empty.
3) A hypothesis that every term of type α is in one of the blocks.
4) A hypothesis that two blocks with non-empty intersection are equal.
-/

/-- The structure of a partition on a Type α. -/ 
@[ext] structure partition (α : Type) :=
(C : set (set α))
(Hnonempty : ∀ X ∈ C, (X : set α).nonempty)
(Hcover : ∀ a, ∃ X ∈ C, a ∈ X)
(Hdisjoint : ∀ X Y ∈ C, (X ∩ Y : set α).nonempty → X = Y)

namespace partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variables {α : Type} {P : partition α} {X Y : set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem equal_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α} (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
-- Proof: follows immediately from the disjointness hypothesis.
P.Hdisjoint _ _ hX hY ⟨a, haX, haY⟩

end partition

section equivalence_classes

/-!

# Definition and basic API for equivalence classes 

We define equivalence classes and prove a few basic results about them.

-/

-- Notation and variables for this section:

-- let α be a type, and let R be an equivalence relation on R.
variables {α : Type} {R : α → α → Prop} (hR : equivalence R)

-- Always assume R is an equivalence relation, even when we don't need it.
include hR

/-- The equivalence class of `x` is the set of `y` related to `x`. -/
def cl (x : α) :=
{y : α | R y x}

/-- Useful for rewriting -- `y` is in the equivalence class of `x` iff
`y` is related to `x`. True by definition. -/
theorem mem_cl_iff {x y : α} : x ∈ cl hR y ↔ R x y := iff.rfl 

/-- x is in cl(x) -/
lemma mem_class_self (x : α) :
  x ∈ cl hR x :=
begin
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  sorry
end

lemma class_sub {x y : α} :
  x ∈ cl hR y →
  cl hR x ⊆ cl hR y :=
begin
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  sorry,
end

lemma class_eq {x y : α} :
  x ∈ cl hR y →
  cl hR x = cl hR y :=
begin
  sorry,
end

end equivalence_classes -- section

/-!

# Statement of the theorem

-/

open partition

-- There is a bijection between equivalence relations on α 
-- and partitions of α
example (α : Type) : {R : α → α → Prop // equivalence R} ≃ partition α :=
-- We define functions in both directions and prove that one is a two-sided
-- inverse of the other
{ -- Here is the first function (construction), from equivalence
  -- relations to partitions.
  -- Let R be an equivalence relation.
  to_fun := λ R, {
    -- Let C be the set of equivalence classes for R.
    C := { B : set α | ∃ x : α, B = cl R.2 x},
    -- I claim that C is a partition. We need to check the three
    -- hypotheses for a partition (`Hnonempty`, `Hcover` and `Hdisjoint`),
    -- so we need to supply three proofs.
    Hnonempty := begin
      -- If X is an equivalence class then X is nonempty.
      show ∀ (X : set α), (∃ (x : α), X = cl _ x) → X.nonempty,
      sorry,
    end,
    Hcover := begin
      -- The equivalence classes cover α
      show ∀ (a : α), ∃ (X : set α) (H : ∃ (x : α), X = cl _ x), a ∈ X,
      sorry
    end,
    Hdisjoint := begin
      -- If two equivalence classes overlap, they are equal.
      show ∀ (X Y : set α), (∃ (x : α), X = cl _ x) →
        (∃ (x : α), Y = cl _ x) → (X ∩ Y).nonempty → X = Y,
      sorry
    end },
  -- Conversely, say P is an partition. 
  inv_fun := λ P, 
    -- Let's define a binary relation by x ~ y iff every block containing a,
    -- also contains b. Because only one block contains a, this will work,
    -- and it turns out to be a nice way of thinking about it. 
    ⟨λ a b, ∀ X ∈ P.C, a ∈ X → b ∈ X, begin
      -- I claim this is an equivalence relation.
    split,
    { -- It's reflexive
      show ∀ (x : α)
        (X : set α), X ∈ P.C → x ∈ X → x ∈ X,
      sorry
    },
    split,
    { -- it's symmetric
      show ∀ (x y : α),
        (∀ (X : set α), X ∈ P.C → x ∈ X → y ∈ X) →
         ∀ (X : set α), X ∈ P.C → y ∈ X → x ∈ X,
      sorry
    },
    { -- it's transitive
      unfold transitive,
      show ∀ (x y z : α),
        (∀ (X : set α), X ∈ P.C → x ∈ X → y ∈ X) →
        (∀ (X : set α), X ∈ P.C → y ∈ X → z ∈ X) →
         ∀ (X : set α), X ∈ P.C → x ∈ X → z ∈ X,
      sorry,
    }
  end⟩,
  -- If you start with the equivalence relation, and then make the partition
  -- and a new equivalence relation, you get back to where you started.
  left_inv := begin
    rintro ⟨R, hrefl, hsymm, htrans⟩,
    -- Tidying up the mess...
    suffices : (λ (a b : α), ∀ (c : α), a ∈ cl _ c → b ∈ cl _ c) = R,
      simpa,
    -- ... you have to prove two binary relations are equal.
    ext a b,
    -- so you have to prove an if and only if.
    show (∀ (c : α), a ∈ cl _ c → b ∈ cl _ c) ↔ R a b,
    sorry
  end,
  -- Similarly, if you start with the partition, and then make the
  -- equivalence relation, and then construct the corresponding partition 
  -- into equivalence classes, you have the same partition you started with.  
  right_inv := begin
    -- Let P be a partition
    intro P,
    -- It suffices to prove that a subset X is in the original partition
    -- if and only if it's in the one made from the equivalence relation.
    ext X,
    show (∃ (a : α), X = cl _ a) ↔ X ∈ P.C,
    sorry,
  end }