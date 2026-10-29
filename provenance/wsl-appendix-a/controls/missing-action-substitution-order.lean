module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P R T : Type} (σ : P → Formula R) (τ : R → Formula T)
    {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.Hom (A.subst σ) (B.subst σ) := Presentation.substitute σ (Presentation.substitute τ f)
