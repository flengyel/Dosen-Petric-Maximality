module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
   (Premise.mix_left (G.identity (P := Nat) (.neg 0)) (G.identity (.neg 0))).parent .right
     (.here (.lit (.neg 0)) []) = some (.here (.lit (.neg 0)) [.lit (.neg 0)]) := by rfl
