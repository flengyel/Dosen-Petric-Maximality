module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (C : NormalForm Empty) :
    (selectedCopies C [[C],[C,C],[C]] []).map At.index = [1,1,6] := by rfl
