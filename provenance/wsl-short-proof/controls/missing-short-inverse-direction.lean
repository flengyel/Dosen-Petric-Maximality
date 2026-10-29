module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (A : Formula P) :
    Presentation.Hom (.conj A (.disj A .top)) (.conj A A) := Presentation.ShortProof.e A
