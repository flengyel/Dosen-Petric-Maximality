module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (BlockedRightConj.gammaBlock (.top : NormalForm Empty) .top (.conj .top .top) [] [] [] []).route.get
      (.here (.conj .top .top) [.conj .top .top,.conj .top .top]) =
    (BlockedRightConj.gammaBlock .top .top (.conj .top .top) [] [] [] []).keep := by rfl
