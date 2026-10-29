module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    ((Formula.var 0 : Formula Nat).subst (fun _ : Nat => (Formula.top : Formula Empty))).Occ := ()
