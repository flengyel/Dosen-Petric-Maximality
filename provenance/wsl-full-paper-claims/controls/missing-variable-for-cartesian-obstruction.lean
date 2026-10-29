module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    ¬ (∀ A B : Formula Empty, Nonempty (ExponentialData (Presentation.operations Empty) A B)) :=
  Presentation.not_cartesian_closed (P:=Empty) ()
