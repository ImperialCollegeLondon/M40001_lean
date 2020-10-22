import tactic
/-! # Two-sided inverses

We define two-sided inverses, and prove that a function
is a bijection if and only if it has a two-sided inverse.

-/

-- let X and Y be types, and let f be a function.
variables {X  Y : Type} (f : X → Y)

-- two-sided inverse
structure two_sided_inverse (f : X → Y) :=
(g : Y → X)
(hX : ∀ x : X, g (f x) = x)
(hY : ∀ y : Y, f (g y) = y)

open function

example : bijective f ↔ nonempty (two_sided_inverse f) :=
begin
  split,
  { intro hf,
    cases hf with hi hs,
    choose g hg using hs,
    let G : two_sided_inverse f :=
    { g := g,
      hX := begin
        intro x,
        apply hi,
        rw hg,
      end,
      hY := begin
        exact hg,
      end
    },
    use G,
  },
  { rintro ⟨g, hX, hY⟩,
    split,
    { intros a b hab,
      apply_fun g at hab,
      rw hX at hab,
      rw hX at hab,
      assumption
    },
    { intro y,
      use (g(y)),
      apply hY,
    }
  }
end
