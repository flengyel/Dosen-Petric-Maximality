module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (FiniteBlocks.decode (fun i : Fin 3 => if i.val=1 then 0 else 1) (1 : Fin 2)).1 = (1 : Fin 3) := by rfl
