import tactic

open function

-- Say we have a collection of animals.
variable (animals : Type)

-- `set Animals` is the type of sets of animals, thought of as photos.

-- Theorem: every way of assigning a photo to each animal is not bijective.
theorem cantor : ∀ f : animals → set animals, ¬ (bijective f) :=
begin
  -- let f be the function which sends each animal to the photo it gets
  intro f,
  -- assume for a contradiction that f is bijective
  intro hf_bij,
  -- then f is injective and surjective
  cases hf_bij with hf_inj hf_surj,
  -- say an animal is happy if they are in the photo they get
  let happy : animals → Prop := λ a, a ∈ f a,
  -- let's make the set of unhappy animals
  let unhappy_animals := {a : animals | ¬ happy a},
  -- f is surjective so let's choose an animal who has this photo
  -- and call him Brian
  cases hf_surj unhappy_animals with brian h_brian,
  -- Sublemma: Brian can't be happy
  have h_not_happy_brian : ¬ happy brian,
  { -- because if he was
    intro h_brian_happy,
    -- then he'd be in his own photo
    have h_fishy : brian ∈ f brian,
      -- because he's happy
      exact h_brian_happy,
    -- so he'd be in the photo of the unhappy animals,
    have h_fishy2 : brian ∈ unhappy_animals,
      -- because that's his photo
      rwa ← h_brian,
    -- which makes him unhappy, a contradiction
    exact h_fishy2 h_brian_happy },
  -- So Brian must be unhappy. But this means he's not in his own photo
  have h_fishy3 : brian ∉ f brian,
    -- by definition of unhappy
    exact h_not_happy_brian,
  -- so he's not in the photo of the unhappy animals
  have h_fishy4 : brian ∉ unhappy_animals,
    -- because that's his photo
    rwa ← h_brian,
  -- and this contradicts the fact that he's unhappy
  exact h_fishy4 h_not_happy_brian,
end

