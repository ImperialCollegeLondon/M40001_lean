import tactic

import data.setoid.partition

--#check setoid.partition.rel_iso

open setoid

variable (α : Type)

-- mathlib has this function already.
/-
def classes (r : setoid α) : set (set α) :=
{s | ∃ y, s = {x | r.rel x y}}
-/
--  set_option pp.notation false

example : {p : set (set α) // is_partition p} ≃
  setoid α :=
{ to_fun := λ pa, { r := λ (a b : α), ∀ X ∈ pa.1, a ∈ X → b ∈ X,
  iseqv :=
  begin
    cases pa with p hp,
    dsimp only at *,
    -- Need to check that the binary relation on α coming from 
    -- a partition p is reflexive, symmetric and transitive
    -- note that p is just the set of sets; hp is the proof
    -- that it's a partition.
    split,
    { -- reflexive
      unfold reflexive,
      cc,
    },
    split,
    { -- symmetric
      -- this needs thought
      -- rintros a b hab X (hX : X ∈ p) hbX,
      -- obtain ⟨Y, ⟨hYp, haY, -⟩, hY2⟩ := hp.2 a, simp at hY2,
      -- have hY3 : ∀ (Z : set α), Z ∈ p → a ∈ Z → Z = Y,
      rintros b c hbc X (hX : X ∈ p) hcX,
      obtain ⟨Y, ⟨hYp, hcY, -⟩, hY2⟩ := hp.2 c, simp at hY2,
      have hpcY : ∀ (Z : set α), Z ∈ p → c ∈ Z → Z = Y,
        simpa using hY2, clear hY2,
      --specialize hab {x | r.rel x y}
      have hXY := hpcY X hX hcX,
      obtain ⟨Z, ⟨hZp, hbZ, -⟩, hZ2⟩ := hp.2 b, simp at hZ2,
      have hcZ := hbc Z hZp hbZ,
      have hZY := hpcY Z hZp hcZ,
      rw [hXY, ← hZY], exact hbZ },
    { -- transitive
      intros b c d hbc hcd X hXp hbX, 
      apply hcd, exact hXp,
      apply hbc;
      assumption,
    }
  end },
  inv_fun := λ r, ⟨classes r,
  begin
    haveI : has_equiv α := ⟨r.rel⟩,
    split,
    { -- empty set isn't an equiv class
      -- proof by contradiction
      intro h,
      cases h with a ha,
      suffices : a ∈ (∅ : set α),
        cases this,
      rw ha,
      simp only [set.mem_set_of_eq],
    },
    { intro a,
      use {x : α | r.rel x a},
      dsimp only,
      split,
      { suffices : {x : α | r.rel x a} ∈ r.classes ∧ r.rel a a,
          simpa,
        split,
          use a,
          refl },
      { intro X,
        rintro ⟨⟨c, rfl⟩, haX, -⟩,
        ext b,
        resetI,
        -- TODO must fix this notation
        change setoid.r b c ↔ r.rel b a,
        change r.rel a c at haX,
        split,
          intro hbc,
          apply r.iseqv.2.2, -- these suck
            exact hbc,
            apply r.iseqv.2.1,
            exact haX,
          -- need a ~ b <-> b ~ a
          intro hba,
          apply r.iseqv.2.2,exact hba, exact haX,
      }
    }
  end⟩,
  left_inv := begin
    rintro ⟨p, hp⟩,
    simp only,
    ext X,
    split,
    { rintro ⟨b, rfl⟩,
      obtain ⟨Y, ⟨hYp, hbY, -⟩, hY2⟩ := hp.2 b,
      have hpb : ∀ (y : set α), y ∈ p → b ∈ y → y = Y,
        simpa using hY2, clear hY2,
      convert hYp,
      ext c,
      obtain ⟨Z, ⟨hZp, hcZ, -⟩, hY2⟩ := hp.2 c,
      have hpc : ∀ (y : set α), y ∈ p → c ∈ y → y = Z,
        simpa using hY2, clear hY2,
      show (∀ X : set α, X ∈ p → c ∈ X → b ∈ X) ↔ _,
      split,
      { intro hpcb,
        specialize hpcb Z hZp hcZ,
        specialize hpb Z hZp hpcb,
        rw ← hpb,
        exact hcZ,
      },
      { intro hcY,
        intros X hXp hcX,
        have hXZ := hpc X hXp hcX,
        have hYZ := hpc Y hYp hcY,
        convert hbY,
        cc } },
    { intro hXp,
      have hX : X.nonempty,
        have h := hp.1,
        rw set.nonempty_iff_ne_empty,
        rintro rfl, contradiction,
      cases hX with b hbX,
      use b,
      ext c,
      simp,
      show c ∈ X ↔ (∀ X : set α, X ∈ p → c ∈ X → b ∈ X),
      split,
      { intros hcX Y hYp hcY,
        convert hbX,
        obtain ⟨Z, ⟨hZp, hcZ, -⟩, hY2⟩ := hp.2 c,
        have hpc : ∀ (y : set α), y ∈ p → c ∈ y → y = Z,
          simpa using hY2, clear hY2,
        have hYZ := hpc Y hYp hcY,
        have hXZ := hpc X hXp hcX,
        cc },
      { intros hcb,
        obtain ⟨Z, ⟨hZp, hcZ, -⟩, hY2⟩ := hp.2 c,
        have hpc : ∀ (y : set α), y ∈ p → c ∈ y → y = Z,
          simpa using hY2, clear hY2, 
        obtain ⟨Y, ⟨hYp, hbY, -⟩, hY2⟩ := hp.2 b,
        have hpb : ∀ (y : set α), y ∈ p → b ∈ y → y = Y,
          simpa using hY2, clear hY2,
        have hZY := hpb Z hZp (hcb Z hZp hcZ),
        have hXY := hpb X hXp hbX,
        cc } }
  end,
  right_inv := begin
    rintro ⟨r, hrr, hrs, hrt⟩,
    ext s,
    simp only [setoid.rel],
    split,
    { intro h,
      specialize h {x : α | r x s} (by use s; refl) (by apply hrr),
      apply hrs,
      exact h },
    { intros hrsb X,
      rintros ⟨c, rfl⟩ h,
      simp [setoid.rel] at h ⊢,
      apply hrt, apply hrs, exact hrsb,
      exact h,
    }
  end }


