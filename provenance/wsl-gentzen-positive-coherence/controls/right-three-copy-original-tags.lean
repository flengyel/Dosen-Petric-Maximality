module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (C : NormalForm Empty) :
    (selectedCopies C [[],[C],[C,C]] [C]).map At.index = [0,2,2] := by rfl
