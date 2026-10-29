module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (C : NormalForm P) (Y F H D E I R : List (NormalForm P))
    (p : Route Y F) (q : Route Y H)
    (l : G P (((F++I)++(H++I))++I) (((D++R)++(E++R))++R)) :
    G P (Y++I) ((D++E)++R) := l
