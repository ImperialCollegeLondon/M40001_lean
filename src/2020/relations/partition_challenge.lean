import data.equiv.basic

structure partition (X : Type) :=
(C : set (set X))
(Hnonempty : ∀ c ∈ C, c ≠ ∅)
(Hcover : ∀ x, ∃ c ∈ C, x ∈ c)
(Hunique : ∀ c d ∈ C, c ∩ d ≠ ∅ → c = d)


def equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R y x}

-- example of use
lemma mem_class {X : Type} {R : X → X → Prop} (HR : equivalence R) (x : X) : x ∈ equivalence_class R x :=
begin
  cases HR with HRR HR,
  exact HRR x,
end

-- here is the bijection between equivalence relations and partitions
example (X : Type) : {R : X → X → Prop // equivalence R} ≃ partition X :=
{ -- Let R be an equivalence relation.
  to_fun := λ R, {
    -- Let C be the set of equivalence classes for R.
    C := { S : set X | ∃ x : X, S = equivalence_class R x},
    -- I claim that C is a partition. We need to check three things.
    Hnonempty := begin
      -- If c is a block then c is nonempty.
      sorry
    end,
    Hcover := begin
      -- The blocks cover X
      sorry
    end,
    Hunique := begin
      -- every element is in at most one of the blocks
      sorry
    end },
  -- Conversely, say P is an partition. 
  inv_fun := λ P, 
    -- Let's define a binary relation by x ~ y iff there's a block they're both in 
    ⟨λ x y, ∃ c ∈ P.C, x ∈ c ∧ y ∈ c, begin
      -- I claim this is an equivalence relation.
    split,
    { -- It's reflexive
      sorry
    },
    split,
    { -- it's symmetric
      sorry
    },
    { -- it's transitive
      sorry
    }
  end⟩,
  -- If you start with the equivalence relation, and then make the partition
  -- and a new equivalence relation, you get back to where you started.
  left_inv := begin
    sorry,
  end,
  -- Similarly, if you start with the partition, and then make the
  -- equivalence relation, and then construct the corresponding partition 
  -- into equivalence classes, you have the same partition you started with.  
  right_inv := begin
    sorry
  end }
