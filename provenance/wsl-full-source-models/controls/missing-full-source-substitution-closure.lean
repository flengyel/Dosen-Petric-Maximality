module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (Q : Presentation.ProofCongruence P)
    {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g) (hfg : Q.Rel f g) : Q.Total :=
  Presentation.maximality Q f g hne hfg
