module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    ((BlockedMix.gammaBlock (.disj .top .top : NormalForm Empty) [] [] [] []).extend [.disj .top .top]).route.get
      (At.shift ([.disj .top .top]++[.disj .top .top]) (.here (.disj .top .top) [])) =
    (BlockedMix.gammaBlock (.disj .top .top) [] [] [] []).keep.before [.disj .top .top] := by rfl
