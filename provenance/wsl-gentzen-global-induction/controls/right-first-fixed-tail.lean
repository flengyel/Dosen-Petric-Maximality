module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (BlockedConjFirst.block (.bot : NormalForm Empty) .top [] [] [.conj .bot .top]).route.get
      (.there (.there (.here (.conj .bot .top) []))) =
        (BlockedConjFirst.block .bot .top [] [] [.conj .bot .top]).keep := by rfl
