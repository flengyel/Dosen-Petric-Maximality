module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
   (LogicalDeletion.headBefore (.there (.here (.top : NormalForm Nat) [])) [.top]).get
     (.here .top [.top,.top]) = .here .top [.top,.top] := by rfl
