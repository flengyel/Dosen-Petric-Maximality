module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    G.cut (G.identity (P:=Nat) (.neg 0)) (G.identity (.neg 0)) = G.identity (.neg 0) := by rfl
