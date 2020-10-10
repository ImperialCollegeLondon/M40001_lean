import data.equiv.basic
import tactic


/-!

# Definition and basic API for partitions

-/

/-- The structure of a partition on a Type α. -/ 
-- Let α be a type. A *partition* on α is defined to
-- be the following data.
@[ext] structure partition (α : Type) :=
-- A set C of subsets of α, called "blocks".
(C : set (set α))
-- A hypothesis (a.k.a. a proof) that all the blocks are non-empty.  
(Hnonempty : ∀ X ∈ C, (X : set α).nonempty)
-- A hypothesis that every term of type α is in one of the blocks.
(Hcover : ∀ a, ∃ X ∈ C, a ∈ X)
-- A hypothesis that two blocks with non-empty intersection are equal.
(Hdisjoint : ∀ X Y ∈ C, (X ∩ Y : set α).nonempty → X = Y)

namespace partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variables {α : Type} {P : partition α} {X Y : set α}

-- a more convenient way of putting it.
theorem Hdisjoint' (hX : X ∈ P.C) (hY : Y ∈ P.C) : (X ∩ Y).nonempty → X = Y :=
P.Hdisjoint X Y hX hY 

-- another way
theorem Hdisjoint'' (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α} (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
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

/-- The equivalence class of `x` is all the `y` such that `y` is related to `x`. -/
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
  exact hrefl x,
end

lemma class_sub {x y : α} :
  x ∈ cl hR y →
  cl hR x ⊆ cl hR y :=
begin
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  intro hxy,
  intro z,
  intro hzx,
  exact htrans hzx hxy,
end

lemma class_eq {x y : α} :
  x ∈ cl hR y →
  cl hR x = cl hR y :=
begin
  intro hxy,
  apply set.subset.antisymm,
    apply class_sub hR hxy,
  apply class_sub hR,
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  exact hsymm hxy,
end

end equivalence_classes -- section

/-!

# Statement of the theorem

-/

open partition

-- There is a bijection between equivalence relations and partitions
example (α : Type) : {R : α → α → Prop // equivalence R} ≃ partition α :=
{ -- Let R be an equivalence relation.
  to_fun := λ R, {
    -- Let C be the set of equivalence classes for R.
    C := { B : set α | ∃ x : α, B = cl R.2 x},
    -- I claim that C is a partition. We need to check three things.
    Hnonempty := begin
      -- If c is a block then c is nonempty.
      rintros c ⟨x, rfl⟩,
      use x,
      apply mem_class_self R.2,
    end,
    Hcover := begin
      intro x,
      use (cl R.2 x),
      split,
      { use x,
      },
      { apply mem_class_self,
      }
    end,
    Hdisjoint := begin
      rintros c d ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨z, hzx, hzy⟩,
      cases R with R hR,
      erw ← class_eq hR hzx,
      erw ← class_eq hR hzy,
    end },
  -- Conversely, say P is an partition. 
  inv_fun := λ P, 
    -- Let's define a binary relation by x ~ y iff there's a block they're both in 
    ⟨λ a b, ∀ X ∈ P.C, a ∈ X → b ∈ X, begin
      -- I claim this is an equivalence relation.
    split,
    { -- It's reflexive
      intros a C hC haC,
      exact haC,
    },
    split,
    { -- it's symmetric
      intros x y h C hC hyC,
      rcases P.Hcover x with ⟨D, hD, hxD⟩,
      convert hxD,
      apply P.Hdisjoint _ _ hC hD,
      use [y, hyC],
      exact h D hD hxD,
    },
    { -- it's transitive
      intros x y z hxy hyx C hC hxC,
      apply hyx C hC,
      apply hxy C hC,
      exact hxC,
    }
  end⟩,
  -- If you start with the equivalence relation, and then make the partition
  -- and a new equivalence relation, you get back to where you started.
  left_inv := begin
    rintro ⟨R, hR⟩,
    simp,
    ext a b,
    rcases hR with ⟨hRr,hRs,hRt⟩,
    split,
    { intro f,
      specialize f a (hRr a),
      exact hRs f,
    },
    { intros hab t hat,
      refine hRt _ hat,
      exact hRs hab,
    },
  end,
  -- Similarly, if you start with the partition, and then make the
  -- equivalence relation, and then construct the corresponding partition 
  -- into equivalence classes, you have the same partition you started with.  
  right_inv := begin
    intro P,
    ext W,
    simp,
    split,
    { rintro ⟨a, rfl⟩,
      rcases P.Hcover a with ⟨X, hX, haX⟩,
      convert hX,
      ext b,
      rw mem_cl_iff,
      split,
      { intro h,
        rcases P.Hcover b with ⟨Y, hY, hbY⟩,
        specialize h Y hY hbY,
        rwa Hdisjoint'' hX hY haX h,
      },
      { intros hbX Y hY hbY,
        rwa Hdisjoint'' hY hX hbY hbX,
      }
    },
    { intro hW,
      cases P.Hnonempty W hW with a haW,
      use a,
      ext b,
      rw mem_cl_iff,
      split,
      { intro hbW,
        intros X hX hbX,
        rwa Hdisjoint'' hX hW hbX hbW
      },
      { intro haX,
        rcases P.Hcover b with ⟨X, hX, hbX⟩,
        specialize haX X hX hbX,
        rwa Hdisjoint'' hW hX haW haX
      }
    }
  end }

