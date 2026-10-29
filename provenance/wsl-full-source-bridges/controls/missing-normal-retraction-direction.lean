module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (X A B : NormalForm P) :
    Hom (.disj (.conj X A) (.conj X B)) (.conj X (.disj A B)) :=
  (NormalRetract.dnfRight X A B).forward
