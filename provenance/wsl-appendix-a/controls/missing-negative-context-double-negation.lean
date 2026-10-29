module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (p : P) (A : Formula P) : Presentation.Hom (.conj A .bot) (.disj A .top) :=
    Presentation.substitute (fun _ : P => .neg A) (Presentation.ManuscriptSubstitution.context (.neg (.var p)))
