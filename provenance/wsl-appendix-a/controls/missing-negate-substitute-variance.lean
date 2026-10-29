module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P R : Type} (σ : P → Formula R) {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.Hom (.neg (A.subst σ)) (.neg (B.subst σ)) := Presentation.substitute σ (Presentation.negate f)
