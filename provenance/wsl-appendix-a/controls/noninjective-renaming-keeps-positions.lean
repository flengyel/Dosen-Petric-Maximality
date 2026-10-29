module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    Formula.renameOcc (fun _ : Nat => ()) (Formula.conj (.var 0) (.var 1)) (Sum.inl ()) =
    Formula.renameOcc (fun _ : Nat => ()) (Formula.conj (.var 0) (.var 1)) (Sum.inr ()) := by rfl
