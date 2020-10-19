import tactic


/-!

# The partition challenge!

Prove that equivalence relations on α are the same as partitions of α.

Three sections:

1) partitions
2) equivalence classes
3) the challenge

Say `α` is a type, and `R` is a binary relation on `α`. 
The following things are already in Lean:

reflexive R := ∀ (x : α), R x x
symmetric R := ∀ ⦃x y : α⦄, R x y → R y x
transitive R := ∀ ⦃x y z : α⦄, R x y → R y z → R x z

equivalence R := reflexive R ∧ symmetric R ∧ transitive R

In the file below, we will define partitions of `α` and "build some
interface" (i.e. prove some propositions). We will define
equivalence classes and do the same thing.
Finally, we will prove that there's a bijection between
equivalence relations on `α` and partitions of `α`.

-/

/-

# 1) Partitions

We define a partition, and prove some easy lemmas.

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

-- docstrings

/-- The set of blocks. -/
add_decl_doc partition.C

/-- Every element of a block is nonempty. -/
add_decl_doc partition.Hnonempty

/-- The blocks cover the type they partition -/
add_decl_doc partition.Hcover

/-- Two blocks which share an element are equal -/
add_decl_doc partition.Hdisjoint

/-

## Basic interface for partitions

-/

namespace partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variables {α : Type} {P : partition α} {X Y : set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem eq_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α} (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
-- Proof: follows immediately from the disjointness hypothesis.
P.Hdisjoint _ _ hX hY ⟨a, haX, haY⟩

/-- If a is in two blocks X and Y, and if b is in X,
  then b is in Y (as X=Y) -/
theorem mem_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a b : α}
  (haX : a ∈ X) (haY : a ∈ Y) (hbX : b ∈ X) : b ∈ Y :=
begin
  -- *great* place to teach convert here
  convert hbX,
  apply eq_of_mem hY hX haY haX,
end


theorem mem_block (a : α) : ∃ X : set α, X ∈ P.C ∧ a ∈ X :=
begin
  -- new tactic
  rcases P.Hcover a with ⟨X, hX, haX⟩,
--  obtain ⟨X, hX, haX⟩ := P.Hcover a,
  use X,
  split,
    assumption,
  exact haX,
end

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
variables {α : Type} (R : α → α → Prop)

/-- The equivalence class of `x` is the set of `y` related to `x`. -/
def cl (x : α) :=
{y : α | R y x}

/-!

## Basic lemmas about equivalence classes

-/

/-- Useful for rewriting -- `y` is in the equivalence class of `x` iff
`y` is related to `x`. True by definition. -/
theorem cl_def {x y : α} : x ∈ cl R y ↔ R x y := iff.rfl 

variables {R} (hR : equivalence R)

include hR

/-- x is in cl(x) -/
lemma mem_cl_self (x : α) :
  x ∈ cl R x :=
begin
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  -- rw on ↔
  rw cl_def,
  -- understand how to use hrefl
  apply hrefl,
end

lemma cl_sub_cl_of_mem_cl {x y : α} :
  x ∈ cl R y →
  cl R x ⊆ cl R y :=
begin
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  intro h,
  rw cl_def at h,
  -- new thing
  -- understand def of subset
  rw set.subset_def,
  intro z,
  intro hzx,
  rw cl_def at hzx ⊢,
  unfold transitive at htrans,
  apply htrans,
    exact hzx,
  exact h,
end

lemma cl_eq_cl_of_mem_cl {x y : α} :
  x ∈ cl R y →
  cl R x = cl R y :=
begin
  intro hxy,
  -- new function, find with library_search
  apply set.subset.antisymm,
    apply cl_sub_cl_of_mem_cl hR,
    assumption,
  apply cl_sub_cl_of_mem_cl hR,
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  apply hsymm,
  assumption,
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
    C := { B : set α | ∃ x : α, B = cl R.1 x},
    -- I claim that C is a partition. We need to check the three
    -- hypotheses for a partition (`Hnonempty`, `Hcover` and `Hdisjoint`),
    -- so we need to supply three proofs.
    Hnonempty := begin
      cases R with R hR,
      -- If X is an equivalence class then X is nonempty.
      show ∀ (X : set α), (∃ (a : α), X = cl R a) → X.nonempty,
      rintros _ ⟨a, rfl⟩,
--      unfold set.nonempty,
      use a,
      rw cl_def,
      rcases hR with ⟨hrefl, hsymm, htrans⟩,
      apply hrefl,
    end,
    Hcover := begin
      cases R with R hR,
      -- The equivalence classes cover α
      show ∀ (a : α), ∃ (X : set α) (H : ∃ (b : α), X = cl R b), a ∈ X,
      intro a,
      use cl R a,
      split,
        use a,
      apply hR.1,
    end,
    Hdisjoint := begin
      cases R with R hR,
      -- If two equivalence classes overlap, they are equal.
      show ∀ (X Y : set α), (∃ (a : α), X = cl R a) →
        (∃ (b : α), Y = cl _ b) → (X ∩ Y).nonempty → X = Y,
      rintros X Y ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
      apply cl_eq_cl_of_mem_cl hR,
      apply hR.2.2,
        apply hR.2.1,
        exact hca,
      exact hcb,
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
      intros a X hXC haX,
      assumption,
    },
    split,
    { -- it's symmetric
      show ∀ (a b : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
         ∀ (X : set α), X ∈ P.C → b ∈ X → a ∈ X,
      intros a b h X hX hbX,
      -- need to know something about how to use partitions.
      obtain ⟨Y, hY, haY⟩ := P.Hcover a,
      specialize h Y hY haY,
      exact mem_of_mem hY hX h hbX haY,
    },
    { -- it's transitive
      unfold transitive,
      show ∀ (a b c : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
        (∀ (X : set α), X ∈ P.C → b ∈ X → c ∈ X) →
         ∀ (X : set α), X ∈ P.C → a ∈ X → c ∈ X,
      intros a b c hbX hcX X hX haX,
      apply hcX, assumption,
      apply hbX, assumption,
      assumption,
    }
  end⟩,
  -- If you start with the equivalence relation, and then make the partition
  -- and a new equivalence relation, you get back to where you started.
  left_inv := begin
    rintro ⟨R, hR⟩,
    -- Tidying up the mess...
    suffices : (λ (a b : α), ∀ (c : α), a ∈ cl R c → b ∈ cl R c) = R,
      simpa,
    -- ... you have to prove two binary relations are equal.
    ext a b,
    -- so you have to prove an if and only if.
    show (∀ (c : α), a ∈ cl R c → b ∈ cl R c) ↔ R a b,
    split,
    { intros hab,
      apply hR.2.1,
      apply hab,
      apply hR.1,
    },
    { intros hab c hac,
      apply hR.2.2,
        apply hR.2.1,
        exact hab,
      exact hac,
    }
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
    split,
    { rintro ⟨a, rfl⟩,
      obtain ⟨X, hX, haX⟩ := P.Hcover a,
      convert hX,
      ext b,
      rw cl_def,
      dsimp,
      split,
      { intro haY,
      obtain ⟨Y, hY, hbY⟩ := P.Hcover b,
      specialize haY Y hY hbY,
      convert hbY,
      exact eq_of_mem hX hY haX haY,
      },
      { intros hbX Y hY hbY,
        apply mem_of_mem hX hY hbX hbY haX,
      }
    },
    { intro hX,
      rcases P.Hnonempty X hX with ⟨a, ha⟩,
      use a,
      ext b,
      split,
      { intro hbX,
        rw cl_def,
        dsimp,
        intros Y hY hbY,
        exact mem_of_mem hX hY hbX hbY ha,
      },
      { rw cl_def,
        dsimp,
        intro haY,
        obtain ⟨Y, hY, hbY⟩ := P.Hcover b,
        specialize haY Y hY hbY,
        exact mem_of_mem hY hX haY ha hbY,
      }
    }
  end }

/-
-- get these files with
leanproject get ImperialCollegeLondon/M40001_lean

-/