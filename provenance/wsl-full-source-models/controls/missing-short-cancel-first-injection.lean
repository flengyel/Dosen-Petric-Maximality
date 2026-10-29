module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (Q : Congruence (Presentation.operations P))
    {A B : Formula P} (f g : Presentation.Hom A B)
    (h : Q.Rel (Presentation.comp f (Presentation.inl B .top))
      (Presentation.comp g (Presentation.inl B .top))) : Q.Rel f g := h
