module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (Y D E Γ Θ I J : List (NormalForm P))
    (p : Route Y D) (q : Route Y E)
    (m : G P (I++((I++Γ)++(I++Θ))) (J++((J++D)++(J++E)))) :
    G P (I++(Γ++Θ)) (J++Y) := m
