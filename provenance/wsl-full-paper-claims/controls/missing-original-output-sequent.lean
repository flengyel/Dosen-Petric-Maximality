module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} {Γ Δ : List (NormalForm P)} (t : G P Γ Δ) :
    G P Δ Γ := Classical.choose (atomized_cut_elimination t)
