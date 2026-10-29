module

public import DosenPetric.SemanticInterpretation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.PresentationSemantics
universe u v w

/-- Dependent congruence keeps the endpoint types in heterogeneous comparisons. -/
theorem heq_apply {A : Type u} {B : A → Sort v} (f : ∀ a, B a)
    {a a' : A} (h : a = a') : HEq (f a) (f a') := by
  cases h
  rfl

theorem heq_apply_two {A : Type u} {B : A → A → Sort v} (f : ∀ a b, B a b)
    {a a' b b' : A} (ha : a = a') (hb : b = b') : HEq (f a b) (f a' b') := by
  cases ha
  cases hb
  rfl

theorem heq_apply_three {A : Type u} {B : A → A → A → Sort v} (f : ∀ a b c, B a b c)
    {a a' b b' c c' : A} (ha : a = a') (hb : b = b') (hc : c = c') :
    HEq (f a b c) (f a' b' c') := by
  cases ha
  cases hb
  cases hc
  rfl

variable {X : Type u} {C : Category.{u,v} X} {O : Objects X}

theorem comp_heq {A B D A' B' D' : X}
    (hA : A = A') (hB : B = B') (hD : D = D')
    {f : C.Hom A B} {f' : C.Hom A' B'} {g : C.Hom B D} {g' : C.Hom B' D'}
    (hf : HEq f f') (hg : HEq g g') : HEq (C.comp f g) (C.comp f' g') := by
  cases hA
  cases hB
  cases hD
  have h₁ : f = f' := eq_of_heq hf
  have h₂ : g = g' := eq_of_heq hg
  cases h₁
  cases h₂
  rfl

theorem tensor_heq (S : Primitives C O) (o : Presentation.Op) {A B D E A' B' D' E' : X}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    {f : C.Hom A D} {f' : C.Hom A' D'} {g : C.Hom B E} {g' : C.Hom B' E'}
    (hf : HEq f f') (hg : HEq g g') : HEq (S.tensor o f g) (S.tensor o f' g') := by
  cases hA
  cases hB
  cases hD
  cases hE
  have h₁ : f = f' := eq_of_heq hf
  have h₂ : g = g' := eq_of_heq hg
  cases h₁
  cases h₂
  rfl

end DosenPetric.PresentationSemantics
