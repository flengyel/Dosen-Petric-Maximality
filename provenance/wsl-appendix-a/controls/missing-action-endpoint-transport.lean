module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P R T : Type} (σ : P → Formula R) (τ : R → Formula T)
    {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.substitute τ (Presentation.substitute σ f) = Presentation.substitute (fun p => (σ p).subst τ) f := by rfl
