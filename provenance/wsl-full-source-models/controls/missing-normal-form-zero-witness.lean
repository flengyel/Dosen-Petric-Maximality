module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (A B : NormalForm P) : Hom A B := finiteUnion (id A) []
