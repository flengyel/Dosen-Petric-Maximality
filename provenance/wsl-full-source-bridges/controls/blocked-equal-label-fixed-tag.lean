module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (BlockedMix.gammaFirstRoute (.top : NormalForm Empty) [.top] [.top] [.top] [.top]).get
      (.here .top [.top]) = .here .top [.top,.top,.top] := by rfl
