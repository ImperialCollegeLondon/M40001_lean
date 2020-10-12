import data.equiv.basic
import tactic


/-!

# The partition challenge!

Prove that equivalence relations on α are the same as partitions of α.

Three sections:

1) partitions
2) equivalence classes
3) the challenge
-/

/-

# 1) Partitions

We define a partition, and then prove one thing about them.

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

/-

## Basic interface for partitions

-/

namespace partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variables {α : Type} {P : partition α} {X Y : set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem equal_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α} (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
-- Proof: follows immediately from the disjointness hypothesis.
P.Hdisjoint _ _ hX hY ⟨a, haX, haY⟩

end partition

/-

# 2) Equivalence classes.

We define equivalence classes and prove a few basic results about them.

-/

section equivalence_classes

/-!

## Definition of equivalence classes 

-/

-- Notation and variables for the equivalence class section:

-- let α be a type, and let R be an equivalence relation on R.
variables {α : Type} {R : α → α → Prop} (hR : equivalence R)

-- Always assume R is an equivalence relation, even when we don't need it.
include hR

/-- The equivalence class of `x` is the set of `y` related to `x`. -/
def cl (x : α) :=
{y : α | R y x}

/-!

## Basic lemmas about equivalence classes

-/

/-- Useful for rewriting -- `y` is in the equivalence class of `x` iff
`y` is related to `x`. True by definition. -/
theorem mem_cl_iff {x y : α} : x ∈ cl hR y ↔ R x y := iff.rfl 

/-- x is in cl(x) -/
lemma mem_cl_self (x : α) :
  x ∈ cl hR x :=
begin
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  sorry,
end

lemma cl_sub_cl_of_mem_cl {x y : α} :
  x ∈ cl hR y →
  cl hR x ⊆ cl hR y :=
begin
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  sorry,
end

lemma cl_eq_cl_of_mem_cl {x y : α} :
  x ∈ cl hR y →
  cl hR x = cl hR y :=
begin
  sorry,
end

end equivalence_classes -- section

/-!

# 3) The challenge!

Let `α` be a type (i.e. a collection of stucff).

There is a bijection between equivalence relations on `α` and
partitions of `α`.

We prove this by writing down constructions in each direction
and proving that the constructions are two-sided inverses of one another.
-/

open partition


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
      cases R with R hR,
      -- If X is an equivalence class then X is nonempty.
      show ∀ (X : set α), (∃ (a : α), X = cl hR a) → X.nonempty,
      sorry,
    end,
    Hcover := begin
      cases R with R hR,
      -- The equivalence classes cover α
      show ∀ (a : α), ∃ (X : set α) (H : ∃ (b : α), X = cl hR b), a ∈ X,
      sorry
    end,
    Hdisjoint := begin
      cases R with R hR,
      -- If two equivalence classes overlap, they are equal.
      show ∀ (X Y : set α), (∃ (a : α), X = cl hR a) →
        (∃ (b : α), Y = cl hR b) → (X ∩ Y).nonempty → X = Y,
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
      show ∀ (a : α)
        (X : set α), X ∈ P.C → a ∈ X → a ∈ X,
      sorry
    },
    split,
    { -- it's symmetric
      show ∀ (a b : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
         ∀ (X : set α), X ∈ P.C → b ∈ X → a ∈ X,
      sorry
    },
    { -- it's transitive
      unfold transitive,
      show ∀ (a b c : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
        (∀ (X : set α), X ∈ P.C → b ∈ X → c ∈ X) →
         ∀ (X : set α), X ∈ P.C → a ∈ X → c ∈ X,
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

/-
-- get these files with

leanproject get ImperialCollegeLondon/M40001_lean

-/