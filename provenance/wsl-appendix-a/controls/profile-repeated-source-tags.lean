module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    PatternProfiles.Example.profiles.a 0 (1 : Fin 3) = PatternProfiles.Example.profiles.a 2 (1 : Fin 3) := by rfl
