module

public import DosenPetric.PresentationShortProjection

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Presentation.ShortProof
universe u v
variable {P : Type u} {R : Type v}

/-- These particular structural isomorphisms commute with every whole-arrow substitution. -/
theorem qTerm_subst (σ : P → Formula R) (A : Formula P) :
    (qTerm A).subst σ = qTerm (A.subst σ) := rfl

theorem qInverseTerm_subst (σ : P → Formula R) (A : Formula P) :
    (qInverseTerm A).subst σ = qInverseTerm (A.subst σ) := rfl

theorem sourceConjTerm_subst (σ : P → Formula R) (X Y A B : Formula P) :
    (sourceConjTerm X Y A B).subst σ =
      sourceConjTerm (X.subst σ) (Y.subst σ) (A.subst σ) (B.subst σ) := rfl

theorem sectionTerm_subst (σ : P → Formula R) (X A B : Formula P) :
    (sectionTerm X A B).subst σ = sectionTerm (X.subst σ) (A.subst σ) (B.subst σ) := rfl

theorem eTerm_subst (σ : P → Formula R) (A : Formula P) :
    (eTerm A).subst σ = eTerm (A.subst σ) := rfl

theorem eInverseTerm_subst (σ : P → Formula R) (A : Formula P) :
    (eInverseTerm A).subst σ = eInverseTerm (A.subst σ) := rfl

theorem q_substitute (σ : P → Formula R) (A : Formula P) : substitute σ (q A) = q (A.subst σ) := rfl

theorem qInverse_substitute (σ : P → Formula R) (A : Formula P) :
    substitute σ (qInverse A) = qInverse (A.subst σ) := rfl

theorem e_substitute (σ : P → Formula R) (A : Formula P) : substitute σ (e A) = e (A.subst σ) := rfl

theorem eInverse_substitute (σ : P → Formula R) (A : Formula P) :
    substitute σ (eInverse A) = eInverse (A.subst σ) := rfl

end DosenPetric.Presentation.ShortProof
