module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} {A B : NormalForm P} (f : Hom A B) : Hom A B :=
  dualHom (dualHom f)
