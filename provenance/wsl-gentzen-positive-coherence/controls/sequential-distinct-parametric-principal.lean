module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (At.here (.conj .top .top : NormalForm Empty) [.conj .top .top]) =
      .there (.here (.conj .top .top) []) := by rfl
