module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example :
    (Route.toTail [.top] (.top : NormalForm Empty)).get (.here .top [.top]) =
      .here .top [.top] := by rfl
