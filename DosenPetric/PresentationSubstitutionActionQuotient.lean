module

public import DosenPetric.PresentationSubstitutionAction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation
universe u v w
variable {P : Type u} {R : Type v} {T : Type w}

/-- Explicit change of the two object indices of an existing source arrow. -/
def transportHom {A B A' B' : Formula P} (hA : A = A') (hB : B = B') (f : Hom A B) : Hom A' B' :=
  hA ▸ hB ▸ f

theorem transportHom_heq {A B A' B' : Formula P} (hA : A = A') (hB : B = B') (f : Hom A B) :
    HEq (transportHom hA hB f) f := by cases hA; cases hB; rfl

theorem ofTerm_heq {A B A' B' : Formula P} (hA : A = A') (hB : B = B')
    {f : Term P A B} {g : Term P A' B'} (h : HEq f g) : HEq (ofTerm f) (ofTerm g) := by
  cases hA; cases hB
  cases eq_of_heq h
  rfl

theorem substitute_identity_heq {A B : Formula P} (f : Hom A B) :
    HEq (substitute Formula.var f) f := by
  induction f using Quotient.inductionOn with
  | h t => exact ofTerm_heq (Formula.subst_identity A) (Formula.subst_identity B) t.subst_identity_heq

theorem substitute_composition_heq (σ : P → Formula R) (τ : R → Formula T)
    {A B : Formula P} (f : Hom A B) :
    HEq (substitute τ (substitute σ f)) (substitute (fun p => (σ p).subst τ) f) := by
  induction f using Quotient.inductionOn with
  | h t =>
    exact ofTerm_heq (Formula.subst_composition σ τ A) (Formula.subst_composition σ τ B)
      (t.subst_composition_heq σ τ)

/-- Identity action as an ordinary equality at the explicit endpoint transports. -/
theorem substitute_identity {A B : Formula P} (f : Hom A B) :
    transportHom (A.subst_identity) (B.subst_identity) (substitute Formula.var f) = f :=
  eq_of_heq ((transportHom_heq _ _ _).trans (substitute_identity_heq f))

/-- Composition action as an ordinary equality at the explicit endpoint transports. -/
theorem substitute_composition (σ : P → Formula R) (τ : R → Formula T)
    {A B : Formula P} (f : Hom A B) :
    transportHom (A.subst_composition σ τ) (B.subst_composition σ τ)
      (substitute τ (substitute σ f)) = substitute (fun p => (σ p).subst τ) f :=
  eq_of_heq ((transportHom_heq _ _ _).trans (substitute_composition_heq σ τ f))

/-- Pointwise equal substitutions act equally, including the endpoint transports. -/
theorem substitute_ext_heq (σ τ : P → Formula R) (h : ∀ p, σ p = τ p)
    {A B : Formula P} (f : Hom A B) : HEq (substitute σ f) (substitute τ f) := by
  have he : σ = τ := funext h
  cases he
  rfl

theorem substitute_ext (σ τ : P → Formula R) (h : ∀ p, σ p = τ p)
    {A B : Formula P} (f : Hom A B) :
    transportHom (A.subst_ext σ τ h) (B.subst_ext σ τ h) (substitute σ f) = substitute τ f :=
  eq_of_heq ((transportHom_heq _ _ _).trans (substitute_ext_heq σ τ h f))

end DosenPetric.Presentation
