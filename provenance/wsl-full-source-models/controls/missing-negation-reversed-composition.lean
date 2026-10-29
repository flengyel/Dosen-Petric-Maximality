module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (A : Formula P) (f g : Presentation.Hom A A) :
    Presentation.negate (Presentation.comp f g) =
      Presentation.comp (Presentation.negate f) (Presentation.negate g) := Presentation.negate_comp f g
