module

public import DosenPetric.ProfileComposition

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.DependentCoordinates
universe u v w z

/-- A dependent block map is injective when its outer map and each fibre map are. -/
theorem sigma_injective {A : Type u} {B : Type v} {F : A → Type w} {G : B → Type z}
    (f : A → B) (hf : ∀ {a a'}, f a = f a' → a = a')
    (g : ∀ a, F a → G (f a)) (hg : ∀ a {x y}, g a x = g a y → x = y)
    {x y : (a : A) × F a}
    (h : (⟨f x.1,g x.1 x.2⟩ : (b : B) × G b) = ⟨f y.1,g y.1 y.2⟩) : x = y := by
  obtain ⟨a,x⟩ := x
  obtain ⟨b,y⟩ := y
  have hab := hf (congrArg Sigma.fst h)
  cases hab
  have hxy := hg a (eq_of_heq (Sigma.mk.inj h).2)
  cases hxy
  rfl

/-- Surjectivity is also fibrewise; no nonempty-fibre hypothesis is needed. -/
theorem sigma_surjective {A : Type u} {B : Type v} {F : A → Type w} {G : B → Type z}
    (f : A → B) (hf : ∀ b, ∃ a, f a = b)
    (g : ∀ a, F a → G (f a)) (hg : ∀ a y, ∃ x, g a x = y)
    (y : (b : B) × G b) : ∃ x : (a : A) × F a,
      (⟨f x.1,g x.1 x.2⟩ : (b : B) × G b) = y := by
  obtain ⟨b,y⟩ := y
  obtain ⟨a,h⟩ := hf b
  cases h
  obtain ⟨x,hx⟩ := hg a y
  exact ⟨⟨a,x⟩,by cases hx; rfl⟩

end DosenPetric.DependentCoordinates
