import data.real.basic

open function

definition pals {X Y Z : Type} (f : X → Y) (g : X → Z) := ∃ h : Y → Z, bijective h ∧ g = h ∘ f

lemma Q5 (X Y Z: Type) (f : X → Y) (g : X → Z) (hf : surjective f) (hg : surjective g) : pals f g ↔ ∀ a b : X, (f a = f b) ↔ (g a = g b) :=
begin
  split,
  { -- if pals then equiv relns equal
    rintro ⟨h, hb, hghf⟩,
      rw funext_iff at hghf,
    intros a b,
    split,
    { -- f(a)=f(b) implies g(a)=g(b)
      intro hfab,
      rw hghf,
      rw hghf,
      show h (f a) = h (f b),
      rw hfab,
    },
    intro hgab,
    cases hb with hi hs,
    apply hi,
    rw hghf at hgab,    
    rw hghf at hgab,    
    exact hgab,
  },
  { intro hequiv,
    unfold pals,
    let hf' := hf,
    choose temp htemp using hf', -- a temporary function Y → X sending y to some random x with f(x)=y
    use g ∘ temp,
    split,
    { split,
      { intros y₁ y₂ h12,
        change g (temp y₁) = g (temp y₂) at h12,
        rw ←hequiv at h12,
        rw htemp at h12,
        rw htemp at h12,
        assumption,
      },
      intro z,
      cases hg z with x hx,
      use f x,
      show g(temp(f(x))) = _,
      rw ←hx,
      rw ←hequiv,
      rw htemp,
    },
    ext,
    show _ = g(temp(f(x))),
    rw ←hequiv,
    rw htemp,
  }
end
